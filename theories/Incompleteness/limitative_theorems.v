From Undecidability.Shared Require Import Dec.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts DecidabilityFacts SemiDecidabilityFacts ReducibilityFacts.

From Equations Require Import Equations.
Require Equations.Type.DepElim.

From FOL Require Import FullSyntax Arithmetics.
From FOL.Proofmode Require Import Theories ProofMode DemoPA.

From FOL.Incompleteness Require Import Axiomatisations utils fol_utils qdec bin_qdec sigma1 epf epf_mu ctq formal_systems fol_incompleteness formula_deduction_utils diagonal_lemma external_provability.

Require FOL.Proofmode.Hoas.
Require Import String Lia List.

Import ListNotations.
Open Scope string_scope. 

Existing Instance PA_funcs_signature.
Existing Instance PA_preds_signature.
Existing Instance full_operators.
Existing Instance falsity_on.

(** * Limitative Theorems *)
(** ** Indefinability *)
Section Indefinability.

    Variables pei: peirce.
    Variables ctq: CTQ.
    Variables göd: goedelisation.

    (* First, we "enable" classical reasoning when proving stable claims (is explicit form really needed?)*)
    Definition stable (P: Prop) := ~~P -> P.

    Lemma stable_classical (P Q: Prop):
      stable Q -> (P \/ ~P -> Q) -> Q.
    Proof.
      unfold stable. tauto.
    Qed.

    (** Definability *)
    Definition defines_pred (φ: form) (P: form -> Prop) (T: form -> Prop) := bounded 1 φ /\ 
      (forall ψ, (P ψ -> T ⊢T φ[(quine_quote ψ)..])) /\ (forall ψ, ~P ψ -> T ⊢T ¬φ[(quine_quote ψ)..]).

    Definition definable (P: form -> Prop) (T: form -> Prop) := exists φ, defines_pred φ P T.

    (** The indefinability theorem: (fun φ => T ⊢T φ) is not definable if T is a consistent extension of Q *)
    Lemma thm_god_not_definable (T: form -> Prop):
     (forall φ, In φ Qeq -> T φ) -> ~ T ⊢T ⊥ ->  ~ definable (fun φ => T ⊢T φ) T. 
    Proof.
      intros Hincl Hconsistent [φ [HBound [HdefL HdefR]]].
      assert (HBound': bounded 1 (¬ φ)). constructor; first assumption. constructor.
      destruct (CTQ_gives_Diagonal_Lemma ctq HBound') as [G [HGBnd HG]].
      eapply stable_classical. Unshelve. 3: exact (T ⊢T G).
        - unfold stable. tauto.
        - intros [HgG | HgG]; apply Hconsistent.
          + specialize (HdefL G).
            destruct (HdefL HgG) as [B [HBincl HBderiv]].
            destruct HgG as [A [HAincl HAderiv]].
            assert (HderivWk: (A ++ B ++ Qeq) ⊢ G). eapply Weak; first eassumption. auto with *. (* Is this good style? *)
            exists (app A (app B Qeq)). split.
              * intros ψ Hψ. destruct (in_app_or _ _ _ Hψ); auto. destruct (in_app_or _ _ _ H); auto.
              * fstart. (* The following is a workaround since fdestruct HG as "[L R]" diverges. *)
                assert (HGWk: (A ++ B ++ Qeq) ⊢ G ↔ (¬ φ)[(quine_quote G)..]). eapply Weak; first eassumption. auto with *. 
                assert (HBderivWk: (A ++ B ++ Qeq) ⊢ φ[(quine_quote G)..]). eapply Weak; first eassumption. auto with *.
                fdestruct HGWk as "[L R]". fapply "L"; first fapply HderivWk. fapply HBderivWk. 
          + exfalso. apply HgG. specialize (HdefR G).
            destruct (HdefR HgG) as [A [HAincl HAderiv]]. exists (app A Qeq). split.
              * intros ψ Hψ. destruct (in_app_or _ _ _ Hψ); auto. 
              * assert (HGWk: (A ++ Qeq) ⊢ G ↔ (¬ φ)[(quine_quote G)..]); eapply Weak; auto with *.
                assert (HAderivWk: (A ++ Qeq) ⊢ ¬ φ[(quine_quote G)..]); eapply Weak; auto with *.
                fstart. fdestruct HGWk as "[L R]". fapply "R". fapply HAderivWk.
    Qed.    
     
    (* This definition is not taken from the literature, just an auxilliary tool. *)
    (* It is definability of P where the backwards directions are also true. *)
    (** Definability, where, in addition, both backwards directions are true *)
    Definition defines_pred_strongly (φ: form) (P: form -> Prop) (T: form -> Prop) := bounded 1 φ /\ 
      (forall ψ, (P ψ <-> T ⊢T φ[(quine_quote ψ)..])) /\ (forall ψ, ~P ψ <-> T ⊢T ¬φ[(quine_quote ψ)..]).

    Definition strongly_definable (P: form -> Prop) (T: form -> Prop) := exists φ, defines_pred_strongly φ P T.

    (** In particular, the indefinability theorem implies that (fun φ => T ⊢T φ) is not strongly definable *)
    Corollary god_not_strongly_definable (T: form -> Prop):
      (forall φ, In φ Qeq -> T φ) -> ~ T ⊢T ⊥ ->  ~ strongly_definable (fun φ => T ⊢T φ) T. 
    Proof.
      intros Hincl Hconsistent [φ [HBound [HdefL HdefR]]].
      apply (thm_god_not_definable Hincl Hconsistent).
      exists φ. repeat split; first assumption.
        - intros ψ Hψ. now apply -> HdefL.
        - intros ψ Hψrefut. now apply HdefR.
    Qed.

    (** Every decidable predicate is strongly definable *)
    Lemma decidable_pred_is_definable (P: form -> Prop) (T: form -> Prop):
      (forall φ, In φ Qeq -> T φ) -> ~T ⊢T ⊥ -> decidable P -> strongly_definable P T.
    Proof.
      intros HIncl Hconsistent HP.
      pose (fun n => P (f n)) as Q.
      assert (decidable Q) as HQ. eapply dec_red. 2: eapply HP. now exists f.
      pose (fun n => ~Q n) as R.
      assert (decidable R) as HR. apply dec_compl. assumption.
      assert (semi_decidable Q /\ semi_decidable R) as [HQs HRs]. auto using decidable_semi_decidable.
      destruct HQ as [fQ HfQ]. destruct HR as [fR HfR].
      assert (Hdisj: forall n, Q n -> R n -> False).
      unfold R. tauto. destruct (ctq_strong_sepr ctq Hdisj HQs HRs) as (τ & HτBound & HτΣ1 & HτQ & HτR).
      exists τ. repeat split.
        - assumption.
        - intros HPn. exists Qeq. split; first auto.
          apply HτQ. unfold Q. now rewrite <- inv_fg.
        - intros Hτn. destruct (fR (g ψ)) eqn:E.
          + apply (HfR (g ψ)) in E. specialize (HτR _ E). exfalso. apply Hconsistent.
            eapply T_IE; last eapply Hτn. exists Qeq. split; first auto. easy.
          + destruct (HfQ (g ψ)) as [HfQL HfQR]. destruct (fQ (g ψ)) eqn:E'; first now rewrite inv_fg.
            exfalso. assert (~R (g ψ)). destruct (HfR (g ψ)) as [HfRL _]. rewrite E in HfRL.
            auto. assert (~Q (g ψ)) by auto. contradiction.
        - intros HPψ. exists Qeq. split; first auto. apply HτR. unfold R.
          unfold Q. now rewrite <- inv_fg.
        - intros Hτ pn. apply Hconsistent. specialize (HτQ (g ψ)).
          eapply T_IE; first eapply Hτ. exists Qeq. split; first auto.
          apply HτQ. unfold Q. now rewrite <- inv_fg.
    Qed.

    (** Essential undecidability: In consistent extensions of Q, provability is not decidable *)
    Corollary essential_undecidability (T: form -> Prop):
      (forall φ, In φ Qeq -> T φ) -> ~T ⊢T ⊥ -> ~ decidable (fun φ => T ⊢T φ).
    Proof.
      intros HIncl Hconsistent [dec_T Hdec_T].
      apply (god_not_strongly_definable HIncl Hconsistent). 
      apply decidable_pred_is_definable. 1-2: assumption.
      exists (fun φ => dec_T φ). intro φ. auto.
    Qed.

End Indefinability.

(** ** Tarski's Theorem *)
Section Tarski.

    Variables ctq: @CTQ intu.
    Variables göd: goedelisation.

    (** Tarski's Theorem: There is no formula true_N(x) such that interp_nat ⊨= φ iff interp_nat ⊨= true_N[(quine_quote φ)..] for all sentences φ *)
    Theorem Tarski's_Theorem:
      ~exists true_N, bounded 1 true_N /\ forall φ, bounded 0 φ -> interp_nat ⊨= φ <-> interp_nat ⊨= true_N[(quine_quote φ)..].
    Proof.
      intros (true_N & HBnd & HRepr).
      assert (bounded 1 (¬ true_N)) as HBnd'. now solve_bounds.
      destruct (CTQ_gives_Diagonal_Lemma ctq HBnd') as [G [HGBnd HG]].
      apply soundness in HG. specialize (HG nat interp_nat (fun n => 0)).
      specialize (HG (nat_is_Q_model (fun _ : nat => 0))).
      cbn in HG. destruct HG as [HGL  HGR]. 
      specialize (HRepr _ HGBnd).
      eapply stable_classical; first firstorder. Unshelve. 2: exact (interp_nat; (fun _ : nat => 0) ⊨ G).
      intros [L | R].
      - apply HGL; first assumption. destruct (HRepr) as [HRepr' _].
        enough (interp_nat ⊨= true_N[(quine_quote G)..]) as H.
        { apply H. }
        apply HRepr. intros ρ. now eapply (sat_closed _ _ _ HGBnd).
      - apply R. apply HGR. intros HTrue.
        assert (interp_nat ⊨= true_N[(quine_quote G)..]) as HTrue'.
        intros ρ. eapply sat_closed. 2: eapply HTrue.
        eapply subst_bounded_max. 2: eassumption.
        { intros [| i] Hi; last lia. now apply qq_closed. }
        apply R. now apply HRepr.
    Qed.
      
End Tarski.
 (** TODO get Tarski's Theorem via Loeb's reasoning *)

(** ** Gödel's First Incompleteness Theorem *)
Section Gödel.

    Variables pei: peirce.
    Variables ctq: CTQ.
    Variables göd: goedelisation.

    (** From the indefinability theorem, we obtain that enumerable, Σ1-sound extesions of Q are incomplete *)
    Corollary godel_first_incompleteness_tarski T:
      enumerable T -> (forall φ, In φ Qeq -> T φ) -> Sig1_sound T -> ~(forall φ, bounded 0 φ -> T ⊩ φ \/ T ⊩ ¬φ).
    Proof.
      intros HEnum HIncl HSound Hcomplete.
      eapply (thm_god_not_definable ctq); first eassumption.
      - now apply Sig1_sound_consistent.
      - destruct (ex_prov_T_util ctq göd HEnum HSound HIncl) as (prov & HprovB & HΣ1 & Hrepr).
        exists prov. repeat split; first assumption.
        + intros ψ Hψ. apply Hrepr. now rewrite <- inv_fg.
        + intros ψ Hψ. assert (bounded 0 prov[(quine_quote ψ)..]) as HprovB'.
          eapply subst_bounded_max. 2: eassumption.
          { intros [| i] Hi; first apply num_bound. lia. }
          destruct (Hcomplete prov[(quine_quote ψ)..]) as [HL | HR]; first assumption.
          * exfalso. apply Hψ. rewrite inv_fg. firstorder.
          * easy.
    Qed. 
    
    (* Enable ProofMode for theories. *)
    Instance eqdec_funcs : EqDec PA_funcs_signature.
    Proof. intros x y; decide equality. Qed.

    Instance eqdec_preds : EqDec PA_preds_signature.
    Proof. intros x y. destruct x, y. now left. Qed.

    Lemma double_neg_elim_class T φ:
      T ⊩C (¬¬φ) -> T ⊩C φ.
    Proof.
      intros HDN. fcontradict. fapply HDN. 
      apply T_Ctx. eapply contains_extend1.
    Qed.

    Lemma contrapositive_elim {p: peirce} T φ ψ:
      T ⊩ (φ ↔ ψ) -> T ⊩ (¬φ) -> T ⊩ (¬ψ).
    Proof.
      intros H1 H2. fstart. fintros "H".
      fapply H2. fapply H1. fapply "H".
    Qed.

    (** By diagonalising against the negation of a sound external provability predicate,
     we find independent sentences for enumerable, Σ1-sound extensions of Q *)
    Corollary godel_first_incompleteness_Sig1_sound (T: form -> Prop):
      enumerable T -> (forall φ, In φ Qeq -> T φ) -> Sig1_sound T -> exists G, bounded 0 G /\ ~T ⊩ G /\ ~T ⊩ ¬G.
    Proof.
      intros HEnum HIncl HSound.
      destruct (ex_prov_T ctq göd HEnum HSound HIncl) as (prov & HΣ1 & Hrepr1 & Hrepr2).
      unfold ext_prov_pred in Hrepr1. destruct Hrepr1 as (HprovB & Hrepr1).
      assert (HsProvB': bounded 1 (¬prov)). now solve_bounds.
      destruct (CTQ_gives_Diagonal_Lemma ctq HsProvB') as (G & HGB & HGE).
      apply list_theory_provability in HGE. eapply (@Weak_T _ _ _ _ _ T _) in HGE.
      2: { intros φ Hφ. unfold Theories.contains in *.
           eauto. }
      cbn in HGE.
      exists G. repeat split; first assumption.
      - intros HG. apply (Sig1_sound_consistent HSound). apply T_CE1 in HGE.
        fstart. fapply HGE; first easy. now apply Hrepr1.
      - enough (~ T ⊩C ¬G) as HGclass.
        { intros HG. apply HGclass. now apply peirce_to_class_theory. }
        intros HG. assert (T ⊩C prov[(num (g G))..]) as Hprov.
        apply double_neg_elim_class. apply peirce_to_class_theory in HGE.
        now eapply contrapositive_elim.
        assert (Σ1 prov[(num (g G))..]) as HΣ1'. now apply Σ1_subst.
        assert (bounded 0 prov[(num (g G))..]) as HprovB'. 
        eapply subst_bounded_max. 2: eassumption. 
        { intros [| i] Hi; first apply num_bound. lia. }
        assert (Sig1_sound T) as HSound' by easy.
        specialize (HSound _ Hprov HprovB' HΣ1').
        apply (Σ1_completeness HΣ1' HprovB') in HSound.
        apply list_theory_provability in HSound.
        eapply WeakT in HSound; last eassumption.
        apply Hrepr2 in HSound. apply peirce_to_class_theory in HSound.
        apply (@Sig1_sound_consistent _ class HSound').
        fstart. fapply HG. fapply HSound.
    Qed.

    (** By diagonalising against ¬sProv(x) from External_Provability.v, 
    there are independent sentences for all enumerable and consistent extensions of Q *)
    Corollary godel_first_incompleteness_strong_sep (T: form -> Prop):
      enumerable T -> (forall φ, In φ Qeq -> T φ) -> ~T ⊩ ⊥ -> exists G, bounded 0 G /\ ~T ⊩ G /\ ~T ⊩ ¬G.
    Proof.
      intros HEnum HIncl HConsistent.
      destruct (ex_sProv_T ctq göd HEnum HConsistent HIncl) as (sProv & HsProvΣ & HsProvReprL & HsProvReprR).
      destruct HsProvReprL as [HsProvB HsProvReprL].
      assert (HsProvB': bounded 1 (¬sProv)). now solve_bounds.
      destruct (CTQ_gives_Diagonal_Lemma ctq HsProvB') as (G & HGB & HGE).
      apply list_theory_provability in HGE. eapply (@Weak_T _ _ _ _ _ T _) in HGE.
      2: { intros φ Hφ. unfold Theories.contains in *.
           eauto. }
      assert (HGE': T ⊩ (G ↔ ¬sProv[(num (g G))..])) by trivial.
      exists G. repeat split; first assumption.
      - intros HG. apply HConsistent. fstart.
        apply T_CE1 in HGE'. fapply HGE'; first easy. now apply HsProvReprL.
      - intros HG. apply HConsistent. fstart. fapply HG.
        apply T_CE2 in HGE'. fapply HGE'. now apply HsProvReprR.
    Qed.

End Gödel.