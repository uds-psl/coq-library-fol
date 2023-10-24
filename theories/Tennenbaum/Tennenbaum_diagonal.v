From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.Shared Require Import ListAutomation.
From FOL.Tennenbaum Require Import MoreDecidabilityFacts Church Coding NumberUtils Formulas SyntheticInType Peano CantorPairing.

(* Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts Formulas Coding Church. *)
Require Import Lia.

Import Vector.VectorNotations.

Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Section Model.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Variable D : Type.
  Variable I : interp D.
  Existing Instance Peano.I'.
  Notation Q := Qeq.

  Notation "⊨ phi" := (forall ρ, ρ ⊨ phi) (at level 21).
  Notation "N⊨ phi" := (forall ρ, @sat _ _ nat interp_nat _ ρ phi) (at level 40).
  Variable axioms : forall ax, PAeq ax -> forall ρ, sat (Peano.I' I) ρ ax.

  Notation "x 'i=' y"  := (@i_atom PA_funcs_signature PA_preds_signature D I Eq ([x ; y])) (at level 40).
  Notation "'iσ' x" := (@i_func PA_funcs_signature PA_preds_signature D I Succ ([x])) (at level 37).
  Notation "x 'i⊕' y" := (@i_func PA_funcs_signature PA_preds_signature D I Plus ([x ; y])) (at level 39).
  Notation "x 'i⊗' y" := (@i_func PA_funcs_signature PA_preds_signature D I Mult ([x ; y])) (at level 38).
  Notation "'i0'" := (i_func (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] ↔ $0 == num (Irred x) ).


  Definition div_num n (d : D) := @Coding.div_num D I n d.
  Definition div_pi n a := @Coding.div_pi D I ψ n a.

  (** * Tennenbaum's Theorem *)
  (** ** Proof via Diagonal Argument *)

  (** Enumerable and discrete PA models have decidable divisibility. *)

  Lemma nat_eq_dec (n m : nat) : {n = m} + {n <> m}.
  Proof. decide equality. Qed.

  Lemma dec_div :
    Enumerable D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros [G Hg] [eq]%Discrete_sum.
    pose (g n := match G n with None => i0 | Some d => d end).
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H' := @iEuclid' D I axioms d (S n) _ in _).
    assert (exists q r, r < S n /\ d = (g q) i⊗ inu (S n) i⊕ inu r) as H.
    { destruct H' as [Q [r ]], (Hg Q) as [q Hq].
      exists q, r. unfold g. now rewrite Hq.
    } clear H'.
    apply ProductWO in H.
    destruct H as [q [r [? Hr]]].
    * destruct (nat_eq_dec r 0) as [E|E].
      + left. exists (g q).
        now rewrite Hr, E, add_zero_r, mult_comm.
      + right. intros [k Hk]. apply E.
        enough (iE : inu r = inu 0).
        { now apply inu_inj in iE. }
        enough ((g q) = k /\ inu r = inu 0) by tauto.
        eapply (@iFac_unique D I axioms).
        -- eapply lt_equiv; eauto.
        -- eapply lt_equiv; auto || lia.
        -- rewrite add_zero, add_comm; auto.
           rewrite <- Hr. rewrite mult_comm. all:eauto.
    * intros x y. apply and_dec; [apply Compare_dec.lt_dec|apply eq].
    Unshelve. lia.
  Qed.


  (**  We can show the same for types that are witnessing and discrete. This is a bit more general, since every enumerable type is witnessing.
   *)
  Lemma dec_div_2 :
    Witnessing D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros wo [eq]%Discrete_sum.
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H := @iEuclid' D I axioms d (S n) _ in _).
    apply wo in H.
    - destruct H as [a Ha].
      apply Witnessing_nat in Ha.
      * destruct Ha as [r [? Hr]].
        destruct (nat_eq_dec r 0) as [E|E].
        + left. exists a.
          now rewrite Hr, E, add_zero_r, mult_comm.
        + right. intros [k Hk]. apply E.
          enough (iE : inu r = inu 0).
          { now apply inu_inj in iE. }
          enough (a = k /\ inu r = inu 0) by tauto.
          unshelve eapply (@iFac_unique D I axioms (inu (S n))).
          -- apply lt_equiv; auto.
          -- apply lt_equiv; auto || lia.
          -- rewrite add_zero. rewrite add_comm.
             rewrite <- Hr. rewrite mult_comm. all: eauto.
      * intros x. apply and_dec; [apply Compare_dec.lt_dec|apply eq].
    - intros ?. apply dec_lt_bounded_exist.
      intros ?. apply eq.
    Unshelve. lia.
  Qed.


  (** Tennenbaum's Theorem via a diagnoal argument. *)

  Fact dec_contraposition A B :
    dec B -> (~B -> ~A) -> (A -> B).
  Proof. intros HB nB a. destruct HB; tauto. Qed.

  Fact Stable_std_stable_stdModel :
    Stable std -> stable (stdModel D).
  Proof.
    intros Hstd H e. apply Hstd. intros He. apply H.
    intros HD. apply He, HD.
  Qed.
  
  Fact Stable_std_negn_nonStd__sdtMobel_equiv :
    Stable std -> stdModel D <-> ~ nonStd D.
  Proof.
    intros stab. split.
    - apply forall__neg_exists_neg.
    - unfold nonStd, stdModel, std.
      apply (Stable_neg_exists_neg__forall); eauto.
  Qed.

  Fact MP_Discrete_stable_std :
    MP -> Discrete D -> Stable std.
  Proof.
    intros mp [eq]%Discrete_sum e. unfold Stable.
    refine (MP_Dec_stable mp _ _).
    constructor. intros ?; apply eq.
  Qed.



  (**  This lemma is similar to the coding lemmas in Coding.v as
      it allows decidable predicates to be coded.
   *)
  Lemma Coding_Dec p :
    @WCT_Q intu -> Stable std -> ~ stdModel D -> Dec p ->
    ~~ exists c, forall n, p n <-> div_pi n c.
  Proof.
    intros wrt%WCT_WRTs ? notStd Dec_p.
    apply (DN_remove (wrt _ Dec_p)).
    intros [ϕ (b1 & _ & H1 & H2)].
    unshelve refine (let H:= @Coding_nonStd_unary _ _ _ _ Hψ _ _ ϕ _ in _); auto.
    apply (DN_chaining H), DN; clear H.
    intros [c Hc].
    exists c; intros n. split.
    + intros H. specialize (Hc n (fun _ => c)) as [Hc1 _].
      apply H1 in H. apply soundness in H.
      unfold div_pi.
      eapply bound_ext with (N:= 2)(sigma:= inu n .: c .: (fun _ => c)).
      { repeat solve_bounds.
        eapply bounded_up; [apply Hψ|lia]. }
      { intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
      cbn in Hc1; apply Hc1.
      unfold valid_ctx in *.
      specialize (H D (Peano.I' I) (fun _ => c)).
      rewrite <-switch_num.
      eapply bound_ext with (N:=0). 3: apply H.
      { eapply subst_bound; eauto. 
        intros []; try lia.
        intros _. apply num_bound. }
      { lia. }
      apply sat_Q_axioms, axioms.
    + specialize (Hc n (fun _ => c)) as [_ Hc2].
      destruct (Dec_p) as [dec_p]; auto.
      apply dec_contraposition; [apply dec_p|].
      intros h [d Hd].
      specialize (H2 _ h). apply soundness in H2.
      eapply H2 with (rho := fun _ => inu 0)(I:= Peano.I' I).
      { apply sat_Q_axioms, axioms. }
      apply switch_num. cbn in Hc2.
      eapply bound_ext with (N:= 1)(sigma:= inu n .: c .: (fun _ => c)).
      { now solve_bounds. }
      intros []; cbn; [reflexivity|lia].
      apply Hc2. exists d. split.
      { eapply bound_ext. apply Hψ. 2: apply Hd.
        intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
      destruct Hd as [_ [k Hk]]. exists k.
      now rewrite Hk.
  Qed.

  Lemma Coding_Dec_ct p :
    @CT_Q intu -> Stable std -> ~ stdModel D ->
    Dec p -> ~~ exists c, forall n, p n <-> div_pi n c.
  Proof. now intros ?%CT_WCT; apply Coding_Dec. Qed.

  (**  We can now use the above coding lemma in combination with RT to
      give a diagonal argument which shows that enumerable and discrete
      PA models must potentially be standard. The double negation can
      actually also be eliminated, and this is done in Variants.v,
      where the needed lemmas are shown.
   *)
  (**  We can still establish the result with the weaker
      assumption of WCT_Q.
   *)
  Theorem Tennenbaum_diagonal :
   @WCT_Q intu -> MP -> Enumerable D -> Discrete D -> forall e, std e.
  Proof.
    intros wct mp enum eq.
    apply Stable_std_stable_stdModel.
    { apply MP_Discrete_stable_std; auto. }
    intros notStd.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    apply (@Coding_Dec p); auto.
    - intros e. apply MP_Dec_stable; auto.
      apply Discrete_sum in eq.
      destruct eq as [eq].
      constructor. intros n. apply eq.
    - unfold p. constructor. intros n.
      destruct (dec_div (Irred n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
    - intros [c' H]. destruct (HG c') as [c Hc].
      specialize (H c). revert H.
      unfold p, g. rewrite Hc.
      tauto.
  Qed.

  Theorem Tennenbaum_diagonal_ct :
    @CT_Q intu -> MP -> Enumerable D -> Discrete D -> forall e, std e.
  Proof. now intros ?%CT_WCT; apply Tennenbaum_diagonal. Qed.


End Model.
