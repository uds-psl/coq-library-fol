From FOL Require Import FullSyntax Arithmetics.
From FOL.Incompleteness Require Import qdec sigma1.
From FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia.
Require Import String List.
Import ListNotations.

Open Scope string_scope.

Module CoqRosser.
Section CoqRosser.

  (* Here we quickly verify the desired property of the Rosser 
     sentence on the level of Coq's logic. *)

  Definition rosser (ϕ ψ: nat -> nat -> Prop) x :=
    exists t, ϕ t x /\ ~ (exists u, u <= t /\ ψ u x).

  Lemma rosser_equiv ϕ ψ x :
    rosser ϕ ψ x <-> (exists t, ϕ t x /\ forall u, ψ u x -> ~ u <= t).
  Proof.
    unfold rosser. split; firstorder.
  Qed.

  Lemma rosser_disj α β x :
    rosser α β x -> rosser β α x -> False.
  Proof.
    intros (t  & H1  & H2 )%rosser_equiv 
           (t' & H1' & H2')%rosser_equiv.
    specialize (H2 _ H1'). specialize (H2' _ H1). lia.
  Qed.

End CoqRosser.
End CoqRosser.


Section prv_utils.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {peirce: peirce}.

  Fact prv_equiv Γ α β :
    Γ ⊢ α ↔ β -> Γ ⊢ α <-> Γ ⊢ β.
  Proof.
    intros Heq. split; intros H; fapply Heq; fapply H.
  Qed.

  Fact curry_to_uncurry ϕ ψ ρ Γ :
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

  (** Definition of the Rosser sentence.  *)
  Definition rosser ϕ ψ := ∃ ϕ ∧ ¬ ∃ $0 ⧀= $1 ∧ ψ[$0 .: $2 ..].
  
  Fact unary_rosser ϕ ψ :
    bounded 2 ϕ -> bounded 2 ψ ->
    bounded 1 (rosser ϕ ψ).
  Proof.
    intros Hϕ Hψ. unfold rosser.
    solve_bounds; auto.
    eapply subst_bounded_max; eauto.
    intros [|[]]; try lia; intros _; solve_bounds.
  Qed. 

  Lemma rosser_equiv ϕ ψ Γ :
    Γ ⊢ rosser ϕ ψ ↔ (∃ ϕ ∧ ∀ ($0 ⧀= $1 → ¬ ψ[$0 .: $2 ..])).
  Proof.
    unfold rosser. fstart. fsplit.
    all: fintros "[x [Hx Hψ]]"; fexists x; fsplit.
    1,3: fapply "Hx".
    - fintros "z". fapply curry_to_uncurry.
      fintros "H". fapply "Hψ". fexists z.
      fapply "H".
    - fintros "[z Hz]". frevert "Hz".
      fapply curry_to_uncurry. fapply "Hψ".
  Qed. 

  Lemma rosser_anitsymmetry Γ :
    Γ ⊢ rosser α β → rosser β α → (∃∃ (¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)).
  Proof.
    fstart. fapply curry_to_uncurry.
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
    fassert (rosser α β → rosser β α → (∃∃ (¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0))) 
      as "Rosser" by fapply rosser_anitsymmetry.
    fintros "H1" "H2". 
    fdestruct ("Rosser" "H1" "H2") as "[w [w' Hww']]".
    fapply prv_lt_lt_bottom in "Hww'". ctx.
  Qed.

  Definition PAQ :=
    ax_zero_succ :: ax_succ_inj :: ax_induction ($0 == zero ∨ (∃ $1 == σ $0)) :: FAeq.

  Lemma PAQ_proves_cases :
    PAQ ⊢ ax_cases.
  Proof.
    unfold PAQ, ax_induction. cbn -[FAeq]. fstart. fapply "H".
    - fleft. fapply ax_refl.
    - fintros x "[H2|H2]".
      + fright. fexists zero. fapply ax_succ_congr. fapply "H2".
      + fdestruct "H2". fright. fexists (σ x0). fapply ax_succ_congr. fapply "H2".
  Qed.
  
  Lemma PA_extends_Q φ Γ :
    (Γ ++ Qeq) ⊢ φ ->
    (forall α, List.In α Γ -> PAeq α) ->
    PAeq ⊢T φ.
  Proof.
    intros H1 H2. exists (List.app Γ PAQ). split.
    - intros psi [H|H] % in_app_iff.
      + now apply H2.
      + destruct H as [<-|[<-|[<-|H]]]; eauto using PAeq.
    - apply (prv_cut H1). intros psi [H|H] % in_app_iff.
      + apply Ctx. apply in_app_iff. now left.
      + apply Weak with PAQ; try now apply incl_appr.
        repeat destruct H as [<-|H]; try destruct H.
        all: try now apply Ctx; unfold PAQ, FAeq, EQ, FA; cbn; auto.
        apply PAQ_proves_cases.
  Qed.

  Theorem rosser_disj :
    PAeq ⊢T rosser α β → rosser β α → ⊥.
  Proof.
    eapply PA_extends_Q; [apply rosser_disj'|].
    intros ax [<-|[]]. apply PAeq_induction.
  Qed.

End Rosser.


Section HA_insep.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Context {peirce: peirce}
          (α: form)         (β: form)
          (Qdec_α: Qdec α)  (Qdec_β: Qdec β)
          (HA2: bounded 2 α)(HB2: bounded 2 β).

  Context (Disj: forall n, Qeq ⊢ (∃ α)[(num n)..] -> Qeq ⊢ (∃ β)[(num n)..] -> False).

  Lemma rosser_inherit n :
    Qeq ⊢ (∃ α)[(num n)..] -> Qeq ⊢ (rosser α β)[(num n)..].
  Proof.
    intros H. simpl in H.
    apply Σ1_witness in H. 2, 3: shelve.
    specialize H as [w Aw].
    unfold rosser. cbn.
    fexists (num w). fsplit; auto.
    apply Σ1_completeness. 1, 2: shelve.
    intros ρ H. apply (@Disj n).
    { fexists (num w). apply Aw. }
    destruct H as [v [_ Hv]]. cbn in Hv.
    apply Σ1_completeness. 1, 2: shelve.
    intros ρ'. exists v.
    rewrite ->!sat_comp in Hv. apply sat_comp.
    eapply (bound_ext _ HB2); [|apply Hv].
    intros [|[]]; try lia || reflexivity.
    intros _. cbn. now rewrite !num_subst, !eval_num. 
    Unshelve.
    { constructor. now apply Qdec_subst. }
    { eapply subst_bounded_max; eauto. 
      intros [|[]]; cbn; try lia; intros _.
      - solve_bounds. 
      - rewrite num_subst. apply num_bound. }
    { constructor. apply Qdec_impl; [|apply Qdec_bot].
      apply Qdec_bounded_exists.
      asimpl. now apply Qdec_subst. }
    { solve_bounds.
      - rewrite !num_subst. apply num_bound.
      - rewrite !subst_comp.
        eapply subst_bounded_max; eauto. 
        intros [|[]]; cbn; try lia; intros _. 
        + solve_bounds. 
        + rewrite !num_subst. apply num_bound. }
    { do 2 constructor. now apply Qdec_subst. }
    { eapply subst_bounded_max with (n:=1).
      - intros []; try lia. intros _. apply num_bound.
      - now constructor. }
  Qed.

End HA_insep.
