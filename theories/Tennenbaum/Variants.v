From FOL Require Import FullSyntax Arithmetics.
From Undecidability.Shared Require Import ListAutomation.

From FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano Tennenbaum_diagonal Tennenbaum_insep HA_insep.
From FOL.Incompleteness Require Import qdec sigma1 ctq.
From FOL.Proofmode Require Import Theories ProofMode.


Require Import Lia.
Require Import String List.
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

  (**  We assume that there is a formula ψ capturing the function
      [Irred] which only produces prime/irreducible numbers.
   *)
  Variable ψ : form.
  Variable Hψ :
    binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).

  (**  We assume that this formula ψ can be used to give an object level 
      proof of the coding theorem that we showed in the standard model.
   *)
  Hypothesis obj_Coding :
    forall α, unary α ->
      PAeq ⊢TI ∀¬¬∃∀ $0 ⧀ $2 → α ↔ ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).

  (** We show the existence of a pair of unary inseparable 
    formulas which are furthermore disjoint on the object level. This
    is quite the strong disjointness property, and critically enables
    the fairly short proofs that will follow.
   *)
  Section HA_insep.

    Definition def_HA_Insep α β :=
        unary α /\ unary β /\
        ( PAeq ⊢TI ¬ ∃ α ∧ β ) /\
        (forall G, Dec G ->
          (forall n, Q ⊢I α[(num n)..] ->   G n) ->
          (forall n, Q ⊢I β[(num n)..] -> ~ G n) ->
          False).

    Lemma invariant_subst_list ρ Γ :
      (forall α : form, α el Γ -> bounded 0 α) ->
      map (subst_form ρ) Γ = Γ.
    Proof.
      induction Γ as [|α Γ IH]; cbn; intros H; [reflexivity|].
      f_equal. 
      2: { apply IH. intros a Ha. apply H; auto. }
      apply bounded_0_subst.
      now apply H.
    Qed.

    Lemma HA_Insep :
      @CT_Q intu -> exists α β, def_HA_Insep α β.
    Proof.
      intros ct.
      eapply CT_Insep_form in ct; eauto.
      destruct ct as (α' & β' & Hα1' & Hα2' & Hβ1' & Hβ2' & H4 & H).
      unfold def_HA_Insep.
      destruct (Σ1_compression Hα1' Hα2') as (α & Hα1 & Hα2 & Hα).
      destruct (Σ1_compression Hβ1' Hβ2') as (β & Hβ1 & Hβ2 & Hβ).
      exists (rosser α β), (rosser β α).
      repeat split.
      - apply unary_rosser; auto.
      - apply unary_rosser; auto.
      - apply PA_extends_Q with [ax_induction (∀ ((¬($0 ⧀= $1)) ∧ ¬($1 ⧀= $0)) → ⊥)]%list.
        2: {  intros a Ha. repeat try (destruct Ha as [<-|Ha]).
              + apply PAeq_induction.
              + destruct Ha. }
        fintros "H". eapply ExE. ctx.
        remember ([ax_induction (∀ ¬ (¬ $0 ⧀= $1) ∧ (¬ $1 ⧀= $0))] ++ Q)%list as Γ.
        cbn -[map]. cbn -[subst_form].
        eapply IE. 2: ctx.
        assert (map (subst_form ↑) Γ = Γ) as ->.
        { apply invariant_subst_list. intros a Ha.
          rewrite HeqΓ in Ha.
          repeat try (destruct Ha as [<-|Ha]); try destruct Ha.
          all: solve_bounds. }
        specialize (@curry_to_uncurry intu) as HH.
        eapply Weak with Γ. 
        2: now do 2 right.
        fapply HH.
        rewrite HeqΓ. unfold Q.
        apply rosser_disj'; auto.
      - intros G HG H1 H2.
        apply (H G HG).
        + intros n Hn. apply H1. apply rosser_inherit; auto.
          * intros x Ha Hb. apply (H4 x).
            split.
            ** eapply equiv_subst. 3: apply Ha. auto.
              fsplit; fintros; fapply Hα; apply Ctx; now left.
            ** eapply equiv_subst. 3: apply Hb. auto.
              fsplit; fintros; fapply Hβ; apply Ctx; now left.
          * eapply equiv_subst. 3: apply Hn. auto.
            fsplit; fintros; fapply Hα; apply Ctx; now left.
        + intros n Hn. apply H2. apply rosser_inherit; auto.
        * intros x Ha Hb. apply (H4 x).
          split.
          ** eapply equiv_subst. 3: apply Hb. auto.
            fsplit; fintros; fapply Hα; apply Ctx; now left.
          ** eapply equiv_subst. 3: apply Ha. auto.
            fsplit; fintros; fapply Hβ; apply Ctx; now left.
        * eapply equiv_subst. 3: apply Hn. auto.
          fsplit; fintros; fapply Hβ; apply Ctx; now left.
    Qed.

  End HA_insep.

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

  (** ** Makholm's Proof *)
  Theorem Makholm :
    @CT_Q intu -> nonStd D -> ~~ exists d, ~ Dec(Div_nat d).
  Proof.
    intros ct [e nstd_e].
    destruct (HA_Insep ct) as (α & β & Hαβ).
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

  (** ** McCarty's Proof *)
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

  Lemma UC_unary_DN_Dec' :
    UC nat bool -> nonStd D ->
    ~ exists α, unary α /\ ~ Dec (fun n => ⊨ α[(num n)..]).
  Proof.
    intros uc [e He] [α [Hα1 HDec]].
    assert (HDec' : ~~~ Dec (fun n : nat => ⊨ α[(num n)..])) by tauto.
    apply HDec'.
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
    @CT_Q intu -> UC nat bool -> ~ nonStd D.
  Proof.
    intros ct uc [e He].
    destruct (HA_Insep ct) as (α & β & Hαβ).
    refine (_ (HA_Insep_undec Hαβ)).
    eapply UC_unary_DN_Dec; eauto. apply Hαβ.
  Qed.

  Lemma UC_Discrete :
    (forall X, UC X bool) -> Discrete D.
  Proof.
    intros uc. unfold Discrete.
    apply UC_Def_Dec. apply uc.
    intros [x y].
    destruct (@Peano.D_eq_dec D I axioms x y); now (left + right).
  Qed.

  Theorem McCarty :
    @CT_Q intu -> (forall X, UC X bool) -> MP -> stdModel D.
  Proof.
    intros ct uc mp.
    specialize (UC_Discrete uc) as HD. 
    unfold stdModel.
    apply Stable_neg_exists_neg__forall; auto.
    - now apply MP_Discrete_stable_std.
    - apply (UC_no_nonStd ct (uc _)).
  Qed.

End McCarty.
End Model.
