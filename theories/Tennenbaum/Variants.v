From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.Shared Require Import ListAutomation.

From FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano Tennenbaum_insep HA_insep.
From FOL.Incompleteness Require Import qdec sigma1 ctq.


Require Import Lia.
Import Vector.VectorNotations.


Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Lemma unary_ext {D} {I: interp D} {α ρ ρ' x} :
  unary α -> sat I (x .: ρ) α -> (x .: ρ') ⊨ α.
Proof.
  intros H_unary H.
  eapply (bound_ext _ H_unary); [|apply H].
  intros []; [reflexivity|lia].
Qed.


Section Model.

Existing Instance PA_preds_signature.
Existing Instance PA_funcs_signature.

  Variable D : Type.
  Variable I : interp D.
  Definition I' := (Peano.I' I).
  Existing Instance I'.
  Notation Q := Qeq.

  Context (axioms : forall ax, PAeq ax -> forall ρ, sat (Peano.I' I) ρ ax).

  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 40).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 38).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  (*  We assume that there is a formula ψ capturing the function
      [Irred] which only produces prime/irreducible numbers.
   *)
  Variable ψ : form.
  Variable Hψ :
    binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).

  (*  We assume that this formula ψ can be used to give an object level 
      proof of the coding theorem that we showed in the standard model.
   *)
  Hypothesis obj_Coding :
    forall α, unary α ->
      PAeq ⊢TI ∀¬¬∃∀ $0 ⧀ $2 → α ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).

  (* Lastly, we will assume the existence of a pair of unary inseparable 
    formulas which are furthermore disjoint on the object level. This
    is quite the strong disjointness property, and critically enables
    the fairly short proofs that will follow.
   *)
  Definition def_HA_Insep α β :=
    unary α /\ unary β /\
      ( PAeq ⊢TI ¬ ∃ α ∧ β ) /\
      (forall G, Dec G ->
        (forall n, Q ⊢I α[(num n)..] ->   G n) ->
        (forall n, Q ⊢I β[(num n)..] -> ~ G n) ->
        False).

  Hypothesis HA_Insep : exists α β, def_HA_Insep α β.

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

  (** Given a pair of object HA-inseparable formulas, we can easily
      show that one of them must be undecidable.
   *)
  Lemma HA_Insep_undec α β :
    def_HA_Insep α β -> ~ Dec (fun n => ⊨ α[(num n)..]).
  Proof.
    intros (Ha1 & Hb1 & Disj & Insepa) Hdec.
    apply (Insepa _ Hdec); intros n H%soundness.
    - intros *; apply H.
      now apply sat_Q_axioms.
    - intros Hα.
      specialize Disj as [Γ [HΓ1 HΓ2%soundness]].
      unshelve refine (let H' := HΓ2 _ _ (fun _ => iO) _ in H' _).
      { intros ? ?%HΓ1. now apply axioms. }
      eexists; split; apply switch_num.
      + apply Hα.
      + now apply H, sat_Q_axioms.
  Qed.

  (** * Makholms Proof of Tennenbaum's Theorem *)
  Theorem Makholm :
    nonStd D -> ~~ exists d, ~ Dec(Div_nat d).
  Proof.
    intros [e nstd_e].
    destruct HA_Insep as (α & β & Hαβ).
    refine (let Ha1 := proj1 Hαβ in
            let undec_α := HA_Insep_undec Hαβ in _ ).
    specialize (obj_Coding Ha1) as [Γ [HΓ1 HΓ2%soundness]].
    pose (ρ := (fun _ : nat => e)).
    unshelve refine (let HΓ3 := HΓ2 D I' ρ _ in _).
    { intros ? H%HΓ1. apply axioms, H. }
    simpl in HΓ3. eapply (DN_chaining (HΓ3 e)), DN.
    intros [c Hc]. exists c. intros [Dec_div].
    clear HΓ1 HΓ2 HΓ3.
    apply undec_α.
    constructor; intros n.
    destruct (Dec_div (Irred n)) as [div|ndiv]; [left|right].
    - intros r.
      specialize (Hc (@inu D I n)) as [_ Hc].
      {apply num_lt_nonStd; auto. }
      apply switch_num. eapply (unary_ext Ha1), Hc.
      refine (ψ_equiv_2 _ _); eauto.
    - intros H. apply ndiv.
      specialize (Hc (@inu D I n)) as [Hc _].
      {apply num_lt_nonStd; auto. }
      specialize (H (c .: e .: ρ)).
      apply switch_num, Hc in H; clear Hc.
      refine (let E := _ in ψ_equiv_1 _ E).
      unfold div_pi. cbn. rewrite E. apply H.
      Unshelve. reflexivity.
Qed.


Section McCarty.

  (** * McCarty Proof of Tennenbaum's Theorem *)
  Lemma unary_DN_bounded_definite ϕ :
    bounded 1 ϕ ->
    forall x, ~ ~ forall y, y i⧀ x -> (fun _ => y) ⊨ ϕ \/ ~ (fun _ => y) ⊨ ϕ.
  Proof.
    intros H1.
    pose (Φ := ¬¬ ∀ $0 ⧀ $1 → ϕ ∨ ¬ ϕ).
    assert (forall d rho, (d .: rho) ⊨ Φ) as H.
    apply induction.
    - apply axioms.
    - repeat solve_bounds; eapply bounded_up; try apply H1; try lia.
    - intros rho. cbn. apply DN.
      now intros y Hy%nolessthen_zero.
    - intros x IHx rho. cbn -[Q] in *.
      specialize (IHx rho).
      assert (~~ ((x .: rho) ⊨ ϕ \/ ~ (x .: rho) ⊨ ϕ) ) as H' by tauto.
      apply (DN_chaining IHx), (DN_chaining H'), DN.
      intros H IH y.
      rewrite lt_S; auto.
      intros [LT| <-].
      + destruct (IH _ LT) as [h|h].
        * left. eapply bound_ext.
          { apply H1. } 2 : apply h.
          intros []; [reflexivity|lia].
        * right. intros h1. apply h.
          eapply bound_ext.
          {apply H1. } 2 : apply h1.
          intros []; [reflexivity|lia].
      + destruct H as [h|h].
        * left. eapply bound_ext.
          {apply H1. } 2 : apply h.
          intros []; [reflexivity|lia].
        * right. intros h1. apply h.
          eapply bound_ext.
          {apply H1. } 2 : apply h1.
          intros []; [reflexivity|lia].
    - intros x.
      specialize (H x (fun _ => i0)). cbn in H.
      apply (DN_chaining H), DN. clear H; intros H.
      intros y Hy. destruct (H _ Hy) as [h|h].
      + left. eapply bound_ext.
        {apply H1. } 2: apply h.
        intros []; [reflexivity|lia].
      + right. intros G. apply h.
        eapply bound_ext.
        {apply H1. } 2: apply G.
        intros []; [reflexivity|lia].
  Qed.

  Lemma UC_unary_DN_Dec α e :
    UC nat bool ->
    unary α -> ~ std e ->
    ~~ Dec (fun n => ⊨ α[(num n)..]).
  Proof.
    intros uc Hα1 He.
    apply (DN_chaining (@unary_DN_bounded_definite _ Hα1 e)), DN.
    intros H. apply UC_Def_Dec; auto.
    intros u.
    specialize (H (@inu _ I u)) as [H|H].
    - apply num_lt_nonStd; auto.
    - left. intros ρ.
      unfold I'. rewrite switch_num.
      eapply bound_ext.
      { apply Hα1. } 2: apply H.
      intros []; [reflexivity|lia].
    - right. intros h. apply H.
      eapply bound_ext.
      { apply Hα1. }
      2: {  specialize (h (fun _ => @inu _ I u)).
            unfold I' in h. rewrite switch_num in h. apply h. }
      intros []; [reflexivity|lia].
  Qed.

  Lemma UC_no_nonStd :
    UC nat bool -> nonStd D -> False.
  Proof.
    intros uc [e He].
    destruct HA_Insep as (α & β & Hαβ).
    refine (_ (HA_Insep_undec Hαβ)).
    eapply UC_unary_DN_Dec; eauto. apply Hαβ.
  Qed.

End McCarty.



End Model.
