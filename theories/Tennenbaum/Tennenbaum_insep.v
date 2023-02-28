From FOL Require Import FullSyntax Arithmetics.
From Undecidability.Shared Require Import ListAutomation.

From FOL.Tennenbaum Require Import MoreDecidabilityFacts DN_Utils Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing.
From FOL.Incompleteness Require Import qdec sigma1 ctq.

From FOL.Proofmode Require Import Theories ProofMode.
Require Import String.
Require Import Lia.
Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Section Model.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Variable D : Type.
  Variable I : interp D.
  Definition I' := (Peano.I' I).
  Existing Instance I'.
  Notation Q := Qeq.

  Variable axioms : forall ax, PAeq ax -> forall ρ, sat (Peano.I' I) ρ ax.

  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 40).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 38).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  (* We also assume the existence of a formula which represents the prime number function *)
  Variable ψ : form.
  Variable Hψ : bounded 2 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  Context (surj_form_ : { Φ : nat -> form & surj Φ })
          (enumerable_Q_prv :
              forall Φ, enumerable (fun n : nat => Q ⊢I (Φ n))).

  Definition Φ := projT1 surj_form_.
  Definition surj_form := projT2 (surj_form_).
  Definition A n := Q ⊢I ¬(Φ n)[(num n)..].
  Definition B n := Q ⊢I (Φ n)[(num n)..].
  (*  We need to work with the intuitionistic deduction system ⊢I here,
      since we want to make use of soundness to prove the next lemma. *)
  Lemma Disjoint_AB : forall n, ~(A n /\ B n).
  Proof.
    unfold A, B. intros n [A_n B_n].
    apply Q_consistent.
    eapply IE; eauto.
  Qed.

  (** Recursively inseparable predicates.  *)

  Definition Insep' :=
    exists A B : nat -> Prop,
      enumerable A /\ enumerable B /\
      (forall n, ~ (A n /\ B n)) /\
      (forall D, Dec D ->
        (forall n, A n ->   D n) ->
        (forall n, B n -> ~ D n) ->
        False).
  
  Definition Insep :=
    exists α β,
      bounded 1 α /\ Σ1 α /\ bounded 1 β /\ Σ1 β /\
      (forall n, ~ (Q ⊢I α[(num n)..] /\ Q ⊢I β[(num n)..]) ) /\
      (forall D, Dec D ->
        (forall n, Q ⊢I α[(num n)..] ->   D n) ->
        (forall n, Q ⊢I β[(num n)..] -> ~ D n) ->
        False).

  Lemma Insep_ :
    @RT_strong intu -> Insep'.
  Proof.
    intros rt.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros G Dec_G.
    destruct  (rt G Dec_G) as [γ [? [? [H1 H2]]]],
              (surj_form γ) as [c Hc].
    rewrite <-Hc in *.
    unfold A, B in *; fold Φ in *.
    do 2 intros ?%(fun h => h c).
    specialize (H1 c); specialize (H2 c).
    tauto.
  Qed.

  Lemma CT_Inseparable :
    @CT_Q intu -> Insep.
  Proof.
    intros ct.
    destruct (Insep_ (CT_RTs ct)) as (A & B & HA & HB & disj & H).
    destruct ((CT_RTw ct) A HA) as [α (? & ? & Ha)],
             ((CT_RTw ct) B HB) as [β (? & ? & Hb)].
    exists α, β.
    repeat split; auto; unfold weak_repr in *.
    - intros n ?. apply (disj n).
      now rewrite Ha, Hb.
    - setoid_rewrite <-Ha.
      setoid_rewrite <-Hb.
      apply H.
  Qed.

  Lemma WInsep_ :
    @WRT_strong intu -> Insep'.
  Proof.
    intros wrt.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros G Dec_G h1 h2.
    specialize (wrt G Dec_G).
    DN.remove_dn.
    destruct wrt as [γ [? [? [H1 H2]]]].
    destruct (surj_form γ) as [c Hc].
    rewrite <-Hc in *.
    unfold A, B in *; fold Φ in *.
    specialize (h1 c); specialize (h2 c).
    specialize (H1 c); specialize (H2 c).
    tauto.
  Qed.


  Lemma WCT_Inseparable :
    @WCT_Q intu -> ~~ Insep.
  Proof.
    intros wct.
    destruct (WInsep_ (WCT_WRTs wct)) as (A & B & HA & HB & disj & H).
    apply (DN_chaining ((WCT_WRTw wct) B HB)),
          (DN_chaining ((WCT_WRTw wct) A HA)), DN.
    intros [α (? & ? & Ha)] [β (? & ? & Hb)].
    exists α, β.
    repeat split; auto; unfold weak_repr in *.
    - intros n ?. apply (disj n).
      now rewrite Ha, Hb.
    - setoid_rewrite <-Ha.
      setoid_rewrite <-Hb.
      apply H.
  Qed.

  Lemma equiv_subst {p: peirce} {Γ α β ρ} :
    map (subst_form ρ) Γ = Γ -> 
    Γ ⊢ α ↔ β -> Γ ⊢ α[ρ] -> Γ ⊢ β[ρ].
  Proof.
    intros HΓ Heq Ha.
    fassert ((α→ β)[ρ]).
    - rewrite <-HΓ.
      eapply subst_Weak. fintros. fapply Heq.
      apply Ctx; now left.
    - cbn. eapply IE.
      + apply Ctx; now left.
      + eapply Weak; eauto. now right.
  Qed.

  Fact prv_iff_symmetry {p: peirce} {Γ α β} :
    Γ ⊢ α ↔ β -> Γ ⊢ β ↔ α.
  Proof.
    intros H. fsplit; fintros; fapply H; apply Ctx; now left.
  Qed.

  Lemma Qdec_kernel_Insep :
    Insep ->
    exists α β,
      bounded 2 α /\ Qdec α /\ bounded 2 β /\ Qdec β /\
      (forall n, ~ (Q ⊢I (∃α)[(num n)..] /\ Q ⊢I (∃β)[(num n)..]) ) /\
      (forall D, Dec D ->
        (forall n, Q ⊢I (∃α)[(num n)..] ->   D n) ->
        (forall n, Q ⊢I (∃β)[(num n)..] -> ~ D n) ->
        False).
  Proof.
    assert (forall ρ, map (subst_form ρ) Q = Q) as HQ.
    { intros ρ. reflexivity. }
    intros (α' & β' & HBa & HSa & HBb & HSb & Disj & H).
    destruct (Σ1_compression HBa HSa) as [α (? & ? & Hα)].
    destruct (Σ1_compression HBb HSb) as [β (? & ? & Hβ)].
    exists α, β. repeat split; try tauto.
    - intros n [Ha Hb]. apply (Disj n).
      split; eapply equiv_subst; auto.
      2 : apply Ha. 3 : apply Hb.
      all : apply prv_iff_symmetry; auto.
    - intros G Dec_G Ha Hb. apply (H G Dec_G).
      + intros n Hn; apply Ha. 
        eapply equiv_subst; eauto.
      + intros n Hn; apply Hb. 
        eapply equiv_subst; eauto.
  Qed.

  Lemma num_le_nonStd n e :
    ~ std e -> exists d : D, e = @inu D I n i⊕ d. 
  Proof.
    intros He. destruct n.
    - exists e. now rewrite add_zero.
    - simpl. setoid_rewrite add_rec; auto.
      now apply num_lt_nonStd.
  Qed. 

  Ltac solve_bounded_sat H :=
    try apply sat_comp; try apply sat_comp in H;
    match goal with
    H : _ ⊨ ?a , B : bounded _ ?a |- _ ⊨ ?a 
        => eapply (bound_ext _ B); [|apply H]
    end.

  (** Potential existence of undecidable predicates. *)
  Lemma Tennenbaum_inseparable :
    Insep -> Stable std ->
    (forall d, ~~ Dec (fun n => div_pi n d)) ->
    nonStd D -> False.
  Proof.
    intros (α & β & HBa & HSa & HBb & HSb & Disj & H)%Qdec_kernel_Insep 
            Hmp HDec [e He].
    (*                  ↓ bound to α     ↓ bound to β     ↓ both   *)
    pose (ϕ := ∀ $0 ⧀= $0`[↑] → ∀ $0 ⧀= $1`[↑] → ∀ $0 ⧀= $2`[↑] → 
                  α[$1..] ∧ β[$2..] → ⊥).
    assert (unary ϕ) as unary_ϕ; [shelve|..].
    eapply Overspill_DN with (alpha:= ϕ); auto. 
    - intros []%He. 
    - intros n ρ. rewrite <-switch_num.
      eapply soundness with (A:=Q).
      2: {now apply sat_Q_axioms. }
      apply Σ1_completeness; [shelve|shelve|].
      intros r w Hw w' Hw' x Hx [H1 H2].
      apply (Disj x). split.
      * apply Σ1_completeness; [shelve|shelve|].
        intros rho. exists w'.
        apply sat_comp.
        asimpl in H1; apply sat_comp in H1.
        eapply bound_ext. 
        3: apply H1. 1: eauto.
        intros [|[]]; try lia; intros _; cbn; auto.
        rewrite num_subst.
        rewrite <-(inu_nat_id x) at 2.
        apply eval_num.
      * apply Σ1_completeness; [shelve|shelve|].
        intros rho. exists w.
        apply sat_comp.
        asimpl in H2. apply sat_comp in H2.
        eapply bound_ext.
        3: apply H2. 1: eauto.
        intros [|[]]; try lia; intros _; cbn; auto.
        rewrite num_subst.
        rewrite <-(inu_nat_id x) at 2.
        apply eval_num.
    - intros [e' He'].
      pose (γ := ∃ $0 ⧀= $2 ∧ α).
      pose (G n := forall ρ, (@inu D I n .: e' .: ρ) ⊨ γ).
      assert (bounded 2 γ) as Hγ; [shelve|].
      refine (let Hcoded := 
        @Coding_nonstd_binary _ _ _ _ Hψ _ Hmp γ _ e' in _).
      DN.remove_dn.
      destruct Hcoded as [c Hc].
      specialize (HDec c).
      DN.remove_dn.
      apply (H G).
      + eapply Dec_transport; eauto.
        intros n. unfold G.
        specialize (Hc n (fun _ => c)) as [H1 H2]. 
        split.
        * intros [k Hk] ρ. eapply bound_ext; [eauto| |apply H2].
          { intros [|[]]; reflexivity || lia. }
          exists k. cbn. split; [|apply Hk].
          change ((k .: inu n .: e' .: c .: (fun _ : nat => c)) ⊨ ψ).
          eapply bound_ext; [apply Hψ| |apply Hk].
          intros [|[]]; reflexivity || lia.
        * intros Hg. destruct H1 as [k Hk]; [apply Hg|].
          exists k. split; [|apply Hk].
          eapply bound_ext; [apply Hψ| |apply Hk].
          intros [|[]]; reflexivity || lia.
      + intros n [w Hw%soundness]%Σ1_witness; [|shelve|shelve].
        fold subst_form in Hw. unfold G.
        intros ρ. exists (@inu D I w). split.
        { cbn. now apply num_le_nonStd. }
        unshelve refine (let Hw' := Hw _ _ (fun _ => e') _ in _).
          { now apply sat_Q_axioms. }
        apply switch_num in Hw'.
        solve_bounded_sat Hw'.
        intros [|[]]; [..|lia]; intros _; auto.
        cbn. rewrite num_subst. symmetry. apply eval_num.
      + intros n [w Hw%soundness]%Σ1_witness Gn; [|shelve|shelve].
        fold subst_form in *.
        specialize (Gn (fun _ => e')) as [k Hk].
        destruct He' as [H1 H2].
        refine (H2 (fun _ => e') (@inu D I w) _ k _ (@inu D I n) _ (conj _ _)).
        1, 3: cbn; now apply num_le_nonStd.
        1: apply Hk.
        * destruct Hk as [_ Hk].
          solve_bounded_sat Hk.
          intros [|[]]; [..|lia]; intros _; auto.
        * unshelve refine (let Hw' := Hw _ _ (fun _ => e') _ in _).
          { now apply sat_Q_axioms. }
          asimpl in Hw'.
          solve_bounded_sat Hw'.
          intros [|[]]; [..|lia]; intros _; symmetry; apply eval_num.
    
    (*  We now settle all of the side conditions that we shelved away
        to keep the structure of the proof at least a bit clearer. *)
    Unshelve.
    { unfold ϕ. unfold unary. solve_bounds.
      1: eapply @bounded_up with (n:=2); try lia.
      2: eapply @bounded_up with (n:=3); try lia.
      all: eapply subst_bound with (N:=2); auto.
      all: intros [|[]]; try lia; intros _; solve_bounds. }
    { constructor. apply Qdec_subst.
      unfold ϕ. do 3 apply Qdec_bounded_forall.
      apply Qdec_impl; [|apply Qdec_bot].
      apply Qdec_and; now apply Qdec_subst. }
    { eapply subst_bound; eauto.
      intros []; [intros _| lia]. apply num_bound. }
    { apply Σ1_subst. now do 2 constructor. }
    { eapply subst_bound.
      - constructor; eauto.
      - intros []; [intros _|lia]. apply num_bound. }
    { apply Σ1_subst. now do 2 constructor. }
    { eapply subst_bound.
      - constructor; eauto.
      - intros []; [intros _|lia]. apply num_bound. }
    { unfold γ. solve_bounds. 
      eapply bounded_up; eauto || lia. }
    { auto. }
    { intros []%He. }
    { auto. }
    { apply Σ1_subst. now constructor. }
    { eapply subst_bound; eauto.
      intros [|[]]; [..|lia]; intros _; solve_bounds.
      cbn; rewrite num_subst; apply num_bound. }
    { apply Σ1_subst. now constructor.  }
    { eapply subst_bound; eauto.
      intros [|[]]; [..|lia]; intros _; solve_bounds.
      cbn; rewrite num_subst; apply num_bound. }
  Qed.

End Model.
