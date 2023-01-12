From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.Shared Require Import ListAutomation.
From FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing.

(* Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts Formulas Coding Church. *)
Require Import Lia.

Import Vector.VectorNotations.


Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.

Lemma unary_ext {D} {I: interp D} {α ρ ρ' x} :
  unary α -> sat I (x .: ρ) α -> (x .: ρ') ⊨ α.
Proof.
  intros H_unary H.
  eapply (bound_ext _ H_unary); [|apply H].
  intros []; [reflexivity|lia].
Qed.

Lemma Qeq_incl_PA α :
  α el Qeq -> PA α.
Proof.
  unfold Qeq. intros H.
  repeat try destruct H as [<-|H].
  1-10: constructor; firstorder.
  {constructor 2. }
  {constructor 3. }
  {constructor 4. }
  firstorder.
Qed.


Section Model.

  Context {Δ1 : Delta1}.

  Variable D : Type.
  Variable I : interp D.
  Local Definition I' : interp D := extensional_model I.
  Existing Instance I | 100.
  Existing Instance I' | 0.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Notation "N⊨ phi" := (forall rho, @sat interp_nat rho phi) (at level 40).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 40).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 38).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  Variable ψ : form.
  Variable Hψ :
    binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).

  Hypothesis obj_Coding :
    forall α, unary α ->
      PA ⊢TI ∀¬¬∃∀ $0 ⧀ $2 → α ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).

  Definition def_obj_Insep α β :=
    unary α /\ unary β /\
      ( PA ⊢TI ¬ ∃ α ∧ β ) /\
      (forall G, Dec G ->
        (forall n, Q ⊢I α[(num n)..] -> G n) ->
        (forall n, ~ (Q ⊢I β[(num n)..] /\ G n)) ->
        False).

  Hypothesis obj_Insep : exists α β, def_obj_Insep α β.


  Definition Div_nat (d : D) := fun n => @Coding.div_num D I n d.
  Definition div_pi := (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  Fact ψ_equiv_1 ρ {n a} :
    (inu n .: ρ) ⊨ div_pi ->
    ρ 0 = a ->
    Coding.div_num I (Irred n) a.
  Proof.
    unfold div_pi. intros H <-.
    specialize H as [d [HH H]]; auto.
    unfold I'.
    enough (d = inu (Irred n)) as ->. apply H.
    eapply ψ_repr; eauto.  
  Qed.

  Fact ψ_equiv_2 n a :
    Coding.div_num I (Irred n) a -> 
    forall ρ, ρ 0 = a -> (inu n .: ρ) ⊨ div_pi.
  Proof.
    intros H ρ <-.
    unfold div_pi. exists (inu (Irred n)).
    unfold I'. split; [|apply H].
    refine (proj2 (ψ_repr _ _ _ _ _) _); auto.
  Qed.

  Theorem Makholm :
    nonStd D -> ~~ exists d, ~ Dec(Div_nat d).
  Proof.
    intros [e nstd_e].
    specialize obj_Insep as (α & β & Ha1 & Hb1 & Disj & Insepa).
    specialize (obj_Coding Ha1) as [Γ [HΓ1 HΓ2%soundness]].
    pose (ρ := (fun _ : nat => e)).
    unshelve refine (let HΓ3 := HΓ2 D I' ρ _ in _).
    { intros ? H%HΓ1. apply axioms, H. }
    simpl in HΓ3. eapply (DN_chaining (HΓ3 e)), DN.
    intros [c Hc]. exists c. intros [Dec_div].
    clear HΓ1 HΓ2 HΓ3.
    eapply (Insepa (fun n => ⊨ α[(num n)..])); clear Insepa.
    - constructor; intros n.
      destruct (Dec_div (Irred n)) as [div|ndiv]; [left|right].
      + intros r.
        specialize (Hc (@inu D I n)) as [_ Hc].
        {apply num_lt_nonStd; auto. }
        apply switch_num. eapply (unary_ext Ha1), Hc.
        refine (ψ_equiv_2 _ _); eauto.
      + intros H. apply ndiv.
        specialize (Hc (@inu D I n)) as [Hc _].
        {apply num_lt_nonStd; auto. }
        specialize (H (c .: e .: ρ)).
        apply switch_num, Hc in H; clear Hc.
        refine (let E := _ in ψ_equiv_1 _ E).
        unfold div_pi. cbn. rewrite E. apply H.
        Unshelve. reflexivity.
    - intros n H%soundness r. apply H.
      intros ??. now apply axioms, Qeq_incl_PA.
    - intros n [H1%soundness H2]. clear Hc Dec_div Γ.
      specialize Disj as [Γ [HΓ1 HΓ2%soundness]].
      unshelve refine (let H := HΓ2 _ _ ρ _ in H _).
      { intros ? H%HΓ1. now apply axioms. }
      eexists; split; apply switch_num.
      + apply H2.
      + apply H1.
        intros ? HQeq; apply axioms, Qeq_incl_PA, HQeq.
  Qed.
End Model.
