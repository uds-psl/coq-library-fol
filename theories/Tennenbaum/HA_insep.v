From FOL Require Import FullSyntax Arithmetics.

From FOL.Tennenbaum Require Import SyntheticInType.
From FOL.Incompleteness Require Import utils fol_utils qdec sigma1.
From FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia.
Require Import String List.
Import ListNotations.

Open Scope string_scope.

Section prv_utils.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {peirce: peirce}.

  Fact curry_no_curry ϕ ψ ρ Γ :
    Γ ⊢ ((ϕ ∧ ψ) → ρ) ↔ (ϕ → (ψ → ρ)).
  Proof.
    fstart; fsplit; fintros "H".
    - fintros "H1" "H2".
      fapply "H". fsplit; fapply "H1" || fapply "H2".
    - fintros "[H1 H2]". fapply "H"; fapply "H1" || fapply "H2".
  Qed. 

  Fact implication_neg_swap ϕ ψ Γ :
    Γ ⊢ (ϕ → ¬ψ) → (ψ → ¬ϕ).
  Proof.
    fstart; fintros "H1" "H2" "H3".
    fapply "H1"; fapply "H2" || fapply "H3".
  Qed.

  Fact prv_contraposition α β Γ :
    Γ ⊢ (α → β) → (¬β → ¬α).
  Proof.
    fstart. fintros "H" "nB" "A".
    fapply "nB". fapply "H". ctx.
  Qed.
End prv_utils.


Section Rosser.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  
  Context {peirce: peirce}.
  Context (α β: form)
          (HA2: bounded 2 α)(HB2: bounded 2 β).
  
  Definition rosser ϕ ψ := ∃ ϕ ∧ ¬ ∃ $0 ⧀= $1 ∧ ψ[$0 .: $2 ..].

  (* 
  Fact unary_rosser ϕ ψ :
    bounded 2 ϕ -> bounded 2 ψ -> 
    bounded 1 (rosser ϕ ψ).
  Proof.
    intros Hϕ Hψ. unfold rosser.
    solve_bounds; auto.
    eapply subst_bounded_max; eauto.
    intros [|[]]; try lia; intros _; solve_bounds.
  Qed. 
  *)

  Lemma rosser_equiv ϕ ψ Γ :
    Γ ⊢ rosser ϕ ψ ↔ (∃ ϕ ∧ ∀ ($0 ⧀= $1 → ¬ ψ[$0 .: $2 ..])).
  Proof.
    unfold rosser. fstart. fsplit.
    all: fintros "[x [Hx Hψ]]"; fexists x; fsplit.
    1,3: fapply "Hx".
    - fintros "z". fapply curry_no_curry.
      fintros "H". fapply "Hψ". fexists z.
      fapply "H".
    - fintros "[z Hz]". frevert "Hz".
      fapply curry_no_curry. fapply "Hψ".
  Qed. 

  Lemma rosser_anitsymmetry Γ :
    Γ ⊢ rosser α β → rosser β α → (∃∃ (¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)).
  Proof.
    fstart. fapply curry_no_curry.
    fintros "[H1 H2]".
    fapply rosser_equiv in "H1".
    fapply rosser_equiv in "H2".
    fdestruct "H1" as "[w [Hw Rw]]".
    fdestruct "H2" as "[w' [Hw' Rw']]".
    fspecialize ("Rw" w').
    fspecialize ("Rw'" w).
    fapply implication_neg_swap in "Rw".
    fapply implication_neg_swap in "Rw'".
    asimpl.
    enough (β[w' .: $0 .: w' .: w..] = β[w' ..]) as ->.
    enough (α[w .: $0 .: w .: w'..] = α[w ..]) as ->.
    fapply "Rw'" in "Hw".
    fapply "Rw" in "Hw'".
    fexists w; fexists w'. fsplit; fapply "Hw" || fapply "Hw'".
    all: eapply bounded_subst; eauto;
          intros [|[]]; reflexivity || lia.
  Qed.

  Goal forall x y, ~(x <= y) /\ ~(y <= x) -> False.
  Proof.
    induction x as [|x IH]; intros y.
    - intros [H1 H2]. apply H1. lia.
    - intros [H1 H2]. destruct y.
      + apply H2. lia.
      + apply (IH y). split.
        * revert H1. lia.
        * revert H2. lia.
  Qed. 

  Lemma prv_0_leq_x :
    Qeq ⊢ ∀ zero ⧀= $0.
  Proof.
    fstart. fintros "x".
    fexists x. fapply ax_sym. fapply ax_add_zero.
  Qed.

  Lemma prv_leq_S :
    Qeq ⊢ ∀∀ $0 ⧀= $1 → (σ $0) ⧀= (σ $1).
  Proof.
    fstart. fintros "x" "z" "[k Hk]".
    fexists k. frewrite "Hk".
    fapply ax_sym. fapply ax_add_rec.
  Qed.

  Lemma prv_lt_lt_bottom :
    (ax_induction (∀ ((¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)) → ⊥) ::
      Qeq) ⊢ (∀∀ ((¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)) → ⊥).
  Proof.
    fstart. unfold ax_induction.
    fapply "H"; fintros "x".
    - fintros "[H1 H2]". fapply "H2".
      fapply prv_0_leq_x.
    - fintros "IH". fintros "z" "[H1 H2]". 
      fassert (z == zero ∨ (∃ z`[↑] == σ $0)) as "z_cases".
      { fapply ax_cases. }
      fdestruct "z_cases".
      + fapply "H1". fexists (σ x).
        frewrite "H0". fapply ax_sym. fapply ax_add_zero.
      + fdestruct "H0" as "[z' Hz']".
        fapply ("IH" z'). fsplit.
        * frevert "H1". frewrite "Hz'".
          fapply prv_contraposition.
          fapply prv_leq_S.
        * frevert "H2". frewrite "Hz'".
          fapply prv_contraposition.
          fapply prv_leq_S.
  Qed.

  Lemma rosser_disj' :
    ([ax_induction (∀ ((¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)) → ⊥)] ++
    Qeq) ⊢ rosser α β → rosser β α → ⊥.
  Proof.
    fstart.
    fassert (rosser α β → rosser β α → (∃∃ (¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0))) as "Rosser" by fapply rosser_anitsymmetry.
    fintros "H1" "H2". 
    fdestruct ("Rosser" "H1" "H2") as "[w [w' Hww']]".
    fapply prv_lt_lt_bottom in "Hww'". ctx.
  Qed.

  Lemma PA_extends_Q φ Γ :
    (Γ ++ Qeq) ⊢ φ ->
    (forall α, List.In α Γ -> PAeq α) ->
    PAeq ⊢T φ.
  Proof.
    intros HQ.
  Admitted.

  Theorem rosser_disj :
    PAeq ⊢T rosser α β → rosser β α → ⊥.
  Proof.
    eapply PA_extends_Q; [apply rosser_disj'|].
    intros ax [<-|[]]. apply PAeq_induction.
  Qed.
  

 (*  
  [ctq.v]
  Lemma sat_PAle ρ s t :
    interp_nat; ρ ⊨ (s ⧀= t) <-> (eval ρ s) <= (eval ρ t).
 *)

End Rosser.


Section HA_insep.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {peirce: peirce}
          (α: form)         (β: form)
          (Qdec_α: Qdec α)  (Qdec_β: Qdec β)
          (HA2: bounded 2 α)(HB2: bounded 2 β).

  Definition α' := ∃ α.
  Definition β' := ∃ β.

  Context (Disj: forall n, Qeq ⊢ α'[(num n)..] -> Qeq ⊢ β'[(num n)..] -> False).

  Lemma rosser_inherit n :
    Qeq ⊢ (∃α)[(num n)..] -> Qeq ⊢ (rosser α β)[(num n)..].
  Proof.
    intros H. simpl in H.
    apply Σ1_witness in H.
    specialize H as [w Aw].
    - unfold rosser. cbn.
      fexists (num w). fsplit; auto.
      apply Σ1_completeness.
      { constructor. apply Qdec_impl; [|apply Qdec_bot].
        apply Qdec_bounded_exists.
        asimpl. now apply Qdec_subst. }
      { admit. }
      intros ρ H. apply (@Disj n).
      + admit.
      + 
    - constructor. now apply Qdec_subst.
    - admit. }
  Admitted.

End HA_insep.