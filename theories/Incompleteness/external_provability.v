From Equations Require Import Equations.
From Undecidability.Shared Require Import Dec.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts MoreReducibilityFacts.

From FOL Require Import FullSyntax Arithmetics.
From FOL.Proofmode Require Import Theories ProofMode.

From FOL.Incompleteness Require Import Axiomatisations utils fol_utils qdec bin_qdec sigma1 epf epf_mu ctq diagonal_lemma formula_deduction_utils.

From FOL Require Proofmode.Hoas.
From Stdlib Require Import String Lia List.
(** * External Provability Predicates *)

Section Ext_prov.

Existing Instance PA_funcs_signature.
Existing Instance PA_preds_signature.
Existing Instance full_operators.
Existing Instance falsity_on.


Variables pei: peirce.
Variables ctq: CTQ.

Variables göd: goedelisation.

(** ** Σ1-soundness *)

Definition Sig1_sound T := forall φ, T ⊢TC φ -> bounded 0 φ -> Σ1 φ -> interp_nat ⊨= φ.

Lemma Sig1_sound_consistent T {p: peirce}:
    Sig1_sound T -> ~T ⊩ ⊥.
Proof.
    intros HSound Hbot. enough (interp_nat ⊨= ⊥) as HSatis.
    { cbn in HSatis. apply HSatis. exact (fun n => 0). }
    apply peirce_to_class_theory in Hbot. apply HSound; first easy.
    - now solve_bounds.
    - constructor. apply Qdec_bot.
Qed.

(** Enumerable predicates in Σ1-sound extensions T of Q are weakly representable in T *)
Lemma Sig1_sound_weak_representability T P:
    (forall φ, In φ Qeq -> T φ) -> enumerable P -> 
    Sig1_sound T -> exists φ,
    bounded 1 φ /\ Σ1 φ /\ forall n, P n <-> T ⊢T φ[(num n)..]. 
Proof.
    intros Hincl Henum Hsound.
    destruct (ctq_weak_repr (ctq_ctq_total ctq) Henum) as (φ & Hbnd & HΣ1 & Hrepr).
    exists φ. repeat split; try easy.
    - intros Hn. eapply WeakT.
      + apply (list_theory_provability Qeq). now apply Hrepr.
      + eauto.
    - intros Hφ. apply Hrepr. assert (Σ1 φ[(num n)..]) as HsubΣ1.
      now apply Σ1_subst. assert (bounded 0 φ[(num n)..]) as Hclosed.
      eapply subst_bounded_max. 2: eassumption. intros i Hi.
      destruct i; first apply num_bound. lia.
      apply Σ1_completeness; try assumption.
      apply peirce_to_class_theory in Hφ.
      now apply Hsound.
Qed.

(** ** Definitions  *)
Definition ext_prov_pred T prov_T := bounded 1 prov_T /\ forall φ, T ⊢T φ -> T ⊢T prov_T[(quine_quote φ)..].
Definition sound_prov_pred T prov_T := ext_prov_pred T prov_T /\ forall φ, T ⊢T prov_T[(quine_quote φ)..] -> T ⊢T φ.

(** ** Enumerability Facts *)
Lemma prv_enum_red T X (h: X -> form):
    enumerable__T X -> enumerable T -> enumerable (fun x => T ⊢T h x).
Proof.
    intros HX HT. assert (enumerable (fun φ => T ⊢T φ)) as HT'.
    apply (@tprv_enumerable PA_funcs_signature PA_preds_signature enumerable_PA_funcs _ enumerable_PA_preds _ T HT pei).
    assert ((fun x => T ⊢T h x) ⪯ (fun φ => T ⊢T φ)) as Hred.
    now exists h.
    eapply enumerable_red; try eassumption.
    apply discrete_iff. constructor. apply dec_form.
    - apply PA_funcs_eq.
    - apply PA_preds_eq.
    - apply dec_full_logic_sym.
    - apply dec_full_logic_quant.
Qed.

Corollary num_tprv_enum T:
    enumerable T -> enumerable (fun n => T ⊢T f n).
Proof.
    apply prv_enum_red. eapply enumerator_enumerable.
    apply enumerator__T_nat.
Qed.

Corollary num_tprv_neg_enum T:
    enumerable T -> enumerable (fun n => T ⊢T ¬f n).
Proof.
    apply prv_enum_red. eapply enumerator_enumerable.
    apply enumerator__T_nat.
Qed.

(** ** Construction of External Provability Predicates *)

Lemma ex_prov_T_util T:
    enumerable T -> Sig1_sound T -> (forall φ, In φ Qeq -> T φ) ->
      exists prov_T, bounded 1 prov_T /\ Σ1 prov_T /\ (forall n, T ⊢T f n <-> T ⊢T prov_T[(num n)..]).
Proof.
    intros Henum Hsound Hincl. apply num_tprv_enum in Henum.
    destruct (Sig1_sound_weak_representability Hincl Henum Hsound) as (prov_T & Hbnd & HΣ1 & Hrepr).
    exists prov_T. repeat split; firstorder.
Qed.

(** A sound external provability predicate *)
Lemma ex_prov_T T:
    enumerable T -> Sig1_sound T -> (forall φ, In φ Qeq -> T φ) ->
      exists prov_T, Σ1 prov_T /\ sound_prov_pred T prov_T.
Proof.
    intros Henum Hsound Hincl.
    destruct (ex_prov_T_util Henum Hsound Hincl) as (prov_T & Hbnd & HΣ1 & Hrepr).
    exists prov_T. unfold sound_prov_pred. unfold ext_prov_pred.
    repeat split; try assumption; intros φ Hφ.
    - apply Hrepr. now rewrite <- inv_fg.
    - rewrite inv_fg. now apply Hrepr.
Qed.

(** An external provability predicate sProv(x) such that also T ⊢ ¬φ -> T ⊢ ¬sProv[(quine_quote φ)..] is satisfied *)
Lemma ex_sProv_T T:
    enumerable T -> ~T ⊢T ⊥ -> (forall φ, In φ Qeq -> T φ) ->
      exists sProv_T, Σ1 sProv_T /\ ext_prov_pred T sProv_T /\
      forall φ, T ⊢T ¬φ -> T ⊢T ¬sProv_T[(quine_quote φ)..].
Proof.
    intros HT Hcons Hincl.
    assert (enumerable (fun n => T ⊢T f n)) as HT'.
    now apply num_tprv_enum.
    apply num_tprv_neg_enum in HT.
    apply enumerable_semi_decidable in HT; last apply discrete_nat.
    apply enumerable_semi_decidable in HT'; last apply discrete_nat.
    assert (forall n, T ⊢T f n -> T ⊢T ¬f n -> False) as Hdisj.
    intros n H1 H2. apply Hcons. eapply T_IE; first eassumption. easy.
    destruct (ctq_strong_sepr ctq Hdisj HT' HT) as (sProv_T & HsProvB & HsProvΣ & HsProvReprL & HsProvReprR). 
    unfold ext_prov_pred. exists sProv_T. repeat split; try assumption; intros φ Hφ.
    - eapply WeakT.
      + apply (list_theory_provability Qeq). apply HsProvReprL. 
        now rewrite <- inv_fg.
      + eauto.
    - eapply WeakT. 
      + apply (list_theory_provability Qeq). apply HsProvReprR. 
        now rewrite <- inv_fg.
      + eauto.
Qed.

End Ext_prov.
