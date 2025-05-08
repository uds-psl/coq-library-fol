From Undecidability.Shared Require Import Dec.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts DecidabilityFacts SemiDecidabilityFacts.

From Equations Require Import Equations.
Require Equations.Type.DepElim.

From FOL Require Import FullSyntax Arithmetics.
From FOL.Proofmode Require Import Theories ProofMode DemoPA.

From FOL.Incompleteness Require Import Axiomatisations utils fol_utils qdec bin_qdec sigma1 epf epf_mu ctq formula_deduction_utils.

Require FOL.Proofmode.Hoas.
Require Import String Lia List Vector.
Import Vector.VectorNotations Vectors.VectorDef.

Import ListNotations.
Open Scope string_scope.

(** * Multivariate CT_Q *)

Section n_ary_ctq.

    Existing Instance PA_funcs_signature.
    Existing Instance PA_preds_signature.
    Existing Instance full_operators.
    Existing Instance falsity_on.

    Variables pei: peirce.
    Variables ctq: CTQ.

    (** * Lemmas for Vectors *)
    Lemma zero_vector_is_nil {X: Type} (v: Vector.t X 0):
    [] = v.
    Proof.
        apply case0. easy.
    Qed. 

    Lemma un_vector_inv {X: Type} n (v: Vector.t X (S n)):
    exists x v', v = x::v'.
    Proof.
        specialize (caseS (fun n vn => exists x v', vn = Vector.cons X x n (v'))) as Ht.
        apply Ht. eauto.
    Qed.

    Lemma bin_vector_inv {X: Type} n (v: Vector.t X (S (S n))):
    exists x y v', v = x::y::v'.
    Proof.
        assert (exists x v0, v = x::v0) as (x0 & v_one & Hx0).
        specialize (caseS (fun n vn => exists x v', vn = Vector.cons X x n (v'))) as Ht.
        apply Ht. eauto.
        assert (exists x v0, v_one = x::v0) as (x1 & v_nil & Hx1).
        specialize (caseS (fun n vn => exists x v', vn = Vector.cons X x n (v'))) as Ht.
        apply Ht. eauto.
        exists x0, x1, v_nil. congruence.
    Qed.

    Lemma vector_inv_two_elems {X: Type} (v: Vector.t X 2):
    exists x y, v = x::y::[].
    Proof.
        destruct (@bin_vector_inv _ _ v) as (x & y & v' & H).
        exists x, y. rewrite <- (zero_vector_is_nil v') in H.
        congruence.
    Qed.

    (** ** Premilinary Definitions *)

    (** Produces the function type nat -> nat -> ... -> nat
        of functions taking (S n) many nats as argument *)
    Fixpoint n_plus_one_ary_function n := match n with
    | 0 => nat -> nat
    | S n => nat -> (n_plus_one_ary_function n)
    end.

    (** Given f: n_plus_one_ary_function (S n)), yields λ m. f (π1 m) (π2 m) *)
    Definition arg_embed n (f: n_plus_one_ary_function (S n)):=
        nat_rec (fun n => n_plus_one_ary_function (S n) -> n_plus_one_ary_function n)
        (fun f m => f (fst (unembed' m)) (snd (unembed' m)))
        (fun _ _ f m => f (fst (unembed' m)) (snd (unembed' m))) n f.

    (** Given f and a vector [x1; x2; ...; xn], computes f x1 x2 ... xn *)
    Definition vector_eval (n: nat) (f: n_plus_one_ary_function n) (nums: t nat (S n)) := 
        nat_rec (fun m : nat => n_plus_one_ary_function m -> t nat (S m) -> nat)
        (fun f nums => f (hd nums))
        (fun n IH f nums => IH (f (hd nums)) (tl nums)) n f nums.

    Lemma embed_eval_interchange n x y nums (f: n_plus_one_ary_function (S n)):
        vector_eval f (x::y::nums) = vector_eval (arg_embed f) (embed' (x, y) :: nums).
    Proof.
        Opaque embed'. Opaque unembed'. 
        destruct n as [|n].
        - assert (nums = []) as ->. symmetry. now apply zero_vector_is_nil.
          cbn. now rewrite unembed'_embed'.
        - cbn. now rewrite unembed'_embed'. 
    Qed.

    (** Given [x1; x2; ...; xn], yields the substitution ((num x1) .: (num x2) .: ... .: (num xn) ..)*)
    Definition n_ary_subst n (nums: t nat (n)) := 
        fold_right (fun n ρ => (num n) .: ρ) nums (var).

    (** ** Substitution Lemmas *)

    Lemma n_ary_subst_update n ψ (x: nat) (nums: t nat n):
        ψ[n_ary_subst (x::nums)] = ψ[(num x)..][n_ary_subst nums].
    Proof.
        cbn. assert (fold_right (fun (n0 : nat) (ρ : nat -> term) => num n0 .: ρ) nums var = n_ary_subst nums) as -> by easy.
        asimpl. now repeat rewrite num_subst.
    Qed.

    Lemma n_ary_subst_update' n ψ (x y: nat) (nums: t nat n):
        ψ[n_ary_subst (x::y::nums)] = ψ[(num x) .: (num y)..][n_ary_subst nums].
    Proof.
        cbn. assert (fold_right (fun (n0 : nat) (ρ : nat -> term) => num n0 .: ρ) nums var = n_ary_subst nums) as -> by easy.
        asimpl. now repeat rewrite num_subst.
    Qed.

    Lemma n_ary_subst_plus_zero_var n φ (nums: t nat n):
        bounded (S n) φ -> φ[n_ary_subst nums][$0..] = φ[n_ary_subst nums].
    Proof.
        revert φ. induction n as [| n IH]; intros φ HBound.
        - assert ([] = nums) as <-. apply zero_vector_is_nil.
          cbn. asimpl. rewrite <- (subst_var φ) at 2.
          eapply bounded_subst; first eassumption. intros k Hk.
          destruct k; easy.
        - destruct (@un_vector_inv _ _ nums) as (x & nums' & ->). 
          rewrite n_ary_subst_update. apply IH.
          eapply subst_bounded_max. 2: eassumption. intros i Hi.
          destruct i; first apply num_bound. constructor. lia.
    Qed.
          

    Lemma subst_deriv_preservance φ k:
        forall (v: t nat k), Qeq ⊢ φ -> Qeq ⊢ φ[n_ary_subst v].
    Proof.
        induction k as [|k IH] in φ |-*.
        - intros v Hφ. rewrite <- (zero_vector_is_nil v). cbn.
          now rewrite (subst_var).
        - intros v Hφ. destruct (@un_vector_inv _ _ v) as (x & v' & ->).
          rewrite (n_ary_subst_update φ).
          assert (Qeq ⊢ φ[(num x)..]) as Hφ'.
          apply Qeq_generalisation in Hφ. fapply Hφ.
          easy.
    Qed.

    (** ** Proof of Multivariate CT_Q *)

    Lemma ctq_n_ary:
        forall n (f: n_plus_one_ary_function n), exists ψ, Σ1 ψ /\ bounded (S (S n)) ψ
            /\ forall (v: t nat (S n)), Qeq ⊢ ∀ ψ[n_ary_subst v] ↔ $0 == num (vector_eval f v). 
    Proof.
        induction n as [|n IH]; intros f.
        - destruct ((ctq_ctq_total ctq) f) as (ψ & HBoundψ & HΣ1ψ & HReprψ).
          exists ψ. repeat split; try assumption. intros v.
          destruct (@un_vector_inv _ _ v) as (n & v_nil & ->).
          assert ([] = v_nil) as <-. apply zero_vector_is_nil. cbn.
          replace (ψ[_]) with (ψ[(num n) .: $0..]); first easy.
          eapply bounded_subst; first eassumption. intros k Hk.
          destruct k; first easy. destruct k; first easy. lia.
        - Opaque n_ary_subst. pose (g:= arg_embed f). fold n_plus_one_ary_function in g.
          destruct (IH g) as [ψ [HΣ1ψ [HBoundψ HReprψ]]].
          destruct (compress_free HBoundψ) as [ρ [HBoundρ HCompress]].
          pose (τ := ψ[ρ]). fold τ in HCompress. exists τ. repeat split.
          + unfold τ. now apply Σ1_subst.
          + assumption.
          + intros nums. apply Qeq_generalisation.
            destruct (@bin_vector_inv _ _ nums) as (x & y & v & Hv).
            specialize (HReprψ ((embed' (x, y))::v)).
            rewrite n_ary_subst_update in HReprψ. cbn in HReprψ.
            specialize (HCompress x y). apply (subst_deriv_preservance v) in HCompress.
            cbn in HCompress. rewrite Hv. rewrite n_ary_subst_update'. fstart.
            fdestruct HCompress as "[L R]". fspecialize (HReprψ $0).
            rewrite num_subst in HReprψ. 
            replace (ψ[_][_][_]) with (ψ[(num (embed' (x, y)))..][n_ary_subst v]) in HReprψ.
            2: { repeat rewrite <- n_ary_subst_update. 
                 symmetry. now apply n_ary_subst_plus_zero_var. }
            fdestruct HReprψ as "[L' R']".
            unfold g. rewrite <- embed_eval_interchange. fsplit.
            * fintros "H". fapply "L'". fapply "R". fapply "H".
            * fintros "H". fapply "L". fapply "R'". fapply "H".
    Qed.

    Transparent n_ary_subst.

    (** ** Binary CT_Q *)

    Corollary binary_ctq (f: nat -> nat -> nat):
        exists ψ, Σ1 ψ /\ bounded 3 ψ 
            /\ forall n m, Qeq ⊢ ∀ ψ[num n .: (num m)..] ↔ $0 == num (f n m).
    Proof.
        specialize (@ctq_n_ary 1) as Hctq. cbn in Hctq.
        destruct (Hctq f) as (ψ & HΣ1ψ & HBoundψ & HReprψ).
        exists ψ. repeat split; try assumption.
        intros n m. now specialize (HReprψ (n::m::[])).
    Qed. 
 

End n_ary_ctq.