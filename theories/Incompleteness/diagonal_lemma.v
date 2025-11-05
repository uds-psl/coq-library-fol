From Undecidability.Shared Require Import Dec.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts DecidabilityFacts SemiDecidabilityFacts.

From Equations Require Import Equations.
Require Equations.Type.DepElim.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Proofmode Require Import Theories ProofMode DemoPA.
From FOL.Incompleteness Require Import Axiomatisations utils fol_utils qdec bin_qdec sigma1 epf epf_mu ctq formula_deduction_utils.
From FOL Require Proofmode.Hoas.
From Stdlib Require Import String Lia List.

Import ListNotations.
Open Scope string_scope.

(** * Diagonal Lemma *)

(** Gödelisation of formulas *)
Class goedelisation {ops: operators} {ff: falsity_flag} {fns: funcs_signature} {prs: preds_signature}:=
     {g: form -> nat; f: nat -> form; inv_fg: forall x, x = f (g x)}. (** If we define this underneath the imports, strange errors occur. *)


Existing Instance PA_funcs_signature.
Existing Instance PA_preds_signature.
Existing Instance full_operators.
Existing Instance falsity_on.

Section Diagonal_Lemma.
    
    Variables pei: peirce.

    (** The numeral of a formula's Gödel number *)
    Definition quine_quote {göd: goedelisation} φ := num (g φ).

    Lemma qq_closed {göd: goedelisation} A:
      bounded_t 0 (quine_quote A).
    Proof.
      unfold quine_quote. apply num_bound.
    Qed.

    Variables göd: goedelisation.

    Implicit Types (A B: form).
    (** ** Preliminary Definitions *)
    (* We define what the diagonalisation of a given formula is. *)

    Definition diagonalisation A := A[(quine_quote A)..].

    Definition diag_nat n := g (diagonalisation (f n)).

    (** Satity check. Diagonalisation on formulas and Gödel numbers coincide *)
    Lemma diag_göd_comm A:
      diag_nat (g A) = g (diagonalisation A).
    Proof.
      unfold diag_nat. rewrite <- inv_fg. reflexivity.
    Qed.

    Lemma subst_bound_2_with_term_subst (ψ: form) (n: nat) (y: term) (sigma: nat -> term) (rho: nat -> term):
        bounded 2 ψ -> ψ[(num n) .: y..] = ψ[(num n)`[rho] .: y .: sigma].
    Proof.
        rewrite num_subst. apply subst_bound_2.
    Qed.

    (** diag_nat is captured by a Σ1-formula φd due to CTQ *)

    Variables φ_D: form.
    Variables φ_D_bound: bounded 2 φ_D.
    Variables φ_D_is_Σ1: Σ1 φ_D.
    Variables φ_D_Hcapt: forall x, Qeq ⊢ ∀ φ_D[num x .: $0..] ↔ $0 == num (diag_nat x).

    (** The formulas F and G as in the thesis, needed to prove the diagonal lemma *)
    Definition diag_F A := ∃ φ_D[$1 .: $0..] ∧ A[$0..].
    Definition diag_G A := diagonalisation (diag_F A).    

    Lemma qq_representation A:
      Qeq ⊢ ∀ φ_D[quine_quote A .: $0..] ↔ $0 == num (g (diagonalisation A)).
    Proof.
      rewrite <- diag_göd_comm. unfold quine_quote. apply φ_D_Hcapt.
    Qed. 

    Lemma diag_G_closed A:
      bounded 1 A -> bounded 0 (diag_G A).
    Proof.
      intros HA. unfold diag_G. unfold diagonalisation.
      unfold diag_F. asimpl. unfold quine_quote.
      rewrite <- subst_bound_2_with_term_subst; last assumption.
      constructor. constructor.
        - eapply subst_bounded_max; last eassumption.
          intros k Hk. destruct k; first apply num_bound.
          destruct k; first (constructor; lia). lia.
        - rewrite <- subst_bound_1; last assumption.
        replace (A[_]) with A.
        2: { pose (fun n => var n) as sigma. symmetry.
             assert (A[$0..] = A[sigma]) as ->.
             eapply bounded_subst; first eassumption.
             intros k Hk. destruct k; easy.
             apply subst_id. easy. }
        assumption.
    Qed.

    (** ** Proof of the Diagonal Lemma *)
    Theorem diagonal_lemma B:
       bounded 1 B -> exists G: form, bounded 0 G /\ Qeq ⊢ G ↔ B[(quine_quote G)..].
    Proof.
    intros HB. exists (diag_G B). split; first apply (diag_G_closed HB). fstart.    
    fsplit.
     - unfold diag_G. unfold diagonalisation. unfold diag_F. cbn. fintros "[x [Hφ HBdiag]]".
       replace (φ_D[_][_][_]) with (φ_D[quine_quote (diag_F B) .: x..]).
       2: { asimpl. apply subst_bound_2. assumption. }
       replace (B[_][_][_]) with (B[x..]).
       2: { asimpl. apply subst_bound_1. assumption. } 
       replace (B[(quine_quote (_))..]) with (B[(quine_quote (diag_G B))..]).
       2: { asimpl. apply subst_bound_1. assumption. }

       specialize (qq_representation (diag_F B)) as HDF. fspecialize (HDF x).
       asimpl in HDF.
       replace (φ_D[_]) with (φ_D[(quine_quote (diag_F B)) .: x..]) in HDF.
       2: { apply subst_bound_2_with_term_subst. assumption. }
       replace (num (_)) with ((num (g (diag_G B)))) in HDF.
       2: { unfold diag_G. unfold diag_F. unfold diagonalisation. asimpl. easy. }
       rewrite num_subst in HDF.
       fdestruct HDF as "[HreprL HreprR]".
       feapply Q_leibniz. 2: fapply "HBdiag".
       unfold quine_quote. fapply "HreprL". fapply "Hφ".
       - fintros "HBdiag". 
         specialize (qq_representation (diag_F B)) as HDF.
         fspecialize (HDF (quine_quote (diag_G B))). rewrite num_subst in HDF. 
         replace (φ_D[_][_]) with (φ_D[(quine_quote (diag_F B)) .: (quine_quote (diag_G B))..]) in HDF.
         2: { asimpl. apply subst_bound_2_with_term_subst. assumption. }
         replace (∃ _) with (diag_G B) in HDF; last easy.
         fdestruct HDF as "[HreprL HreprR]". fexists (quine_quote (diag_G B)). 
         replace (φ_D[_][_][_]) with (φ_D[(quine_quote (diag_F B)) .: (quine_quote (diag_G B))..]).
         2: { asimpl. apply subst_bound_2. assumption. }
         replace (B[_][_][_]) with (B[(quine_quote (diag_G B))..]).
         2: { asimpl. apply subst_bound_1. assumption. }
         fsplit.
          + fapply "HreprR". (* Why are definitions unfolded here? *)
            unfold quine_quote. fapply ax_refl. 
          + fapply "HBdiag".
    Qed.


End Diagonal_Lemma.

(** Wrapper to access the diagonal lemma directly. Used as interface for other theories relying onthe diagonal lemma *)
Lemma CTQ_gives_Diagonal_Lemma {pei: peirce} {göd: goedelisation}:
    CTQ -> forall B, bounded 1 B -> exists G, bounded 0 G /\ Qeq ⊢ G ↔ B[(quine_quote G)..].
Proof.
    intros HCTQ. apply ctq_ctq_total in HCTQ. 
    destruct (HCTQ (diag_nat göd)) as (φ_D & Hφ_D_Bound & Hφ_D_Σ1 & Hφ_D_repr).
    eapply diagonal_lemma; eassumption.
Qed.

(** Carnap's diagonalisation equivalence *)
Lemma diagonalisation_equivalence {göd: goedelisation}:
    @CTQ intu -> forall B, bounded 1 B -> exists G, bounded 0 G /\ interp_nat ⊨= (G ↔ B[(quine_quote G)..]).
Proof.
    intros HCTQ H HB. specialize (CTQ_gives_Diagonal_Lemma HCTQ HB) as [G [HGBnd HGequiv]].
    apply soundness in HGequiv. exists G. split; first assumption.
    intros ρ. specialize (HGequiv nat interp_nat ρ). apply HGequiv.
    intros φ Hφ. now apply nat_is_Q_model.
Qed.

(** ** Counterexamples from Generalised Diagonal Lemma *)
Lemma Diagonal_Lemma_mult_counterexample {pei: peirce} {göd: goedelisation}:
    ~exists G, Qeq ⊢ G ↔ quine_quote G == quine_quote G /\ Qeq ⊢ G ↔ quine_quote  G== σ (quine_quote G).
Proof.
    intros [G [HG1 HG2]]. 
    assert (Qeq ⊢ num (g G) == σ (num (g G))) as Heq.
    fapply HG2. fapply HG1. fapply ax_refl.
    eapply Σ1_soundness in Heq.
    Unshelve. 4: exact (fun _ => 0).
    2: { constructor. apply Qdec_eq. }
    2: { solve_bounds; apply num_bound. }
    cbn in Heq. now repeat rewrite nat_eval_num in Heq.
Qed.

Local Ltac close HG HB := rewrite num_subst in HG; now rewrite (bounded_0_subst _ HB) in HG.

Lemma Diagonal_Lemma_bound_counterexample {pei: peirce} {göd: goedelisation}:
    ~exists G, bounded 0 G /\ Qeq ⊢ G ↔ quine_quote G == $0.
Proof.
    unfold quine_quote.
    intros [G [HB HG]]. apply Qeq_generalisation in HG.
    apply Diagonal_Lemma_mult_counterexample.
    exists G; split.
    - fspecialize (HG (num (g G))). close HG HB.
    - fspecialize (HG (σ (num (g G)))). close HG HB.
Qed.
