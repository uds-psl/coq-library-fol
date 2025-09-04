From Undecidability Require Import Synthetic.EnumerabilityFacts Synthetic.ListEnumerabilityFacts Shared.ListAutomation.
Require Import FOL.Completeness.TarskiCompleteness.
Require Import FOL.ModelTheory.FragmentCore.
Local Set Implicit Arguments.

(** * Henkin Model (Negative Fragement) *)


(* Gives the proof that any model with term as domain is countable. 
   It may be possible to generalize to arbitrary cardinality depandent
   on signature. *)
   
Section TermIsCountable.
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.

    (* Proof of countable *)
    Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
    Variable eF : nat -> option Σf.
    Context {HeF : enumerator__T eF Σf}.
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Variable list_Funcs : nat -> list syms.
    Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.

    Lemma term_model_countable: a_coutable_model term.
    Proof.
        destruct (enumT_term enum_Funcs') as [f H]. 
        exists (fun n => match f n with None => var n | Some t => t end).
        intro t. destruct (H t) as [n eq].
        exists n. now rewrite eq.
    Qed.


    (* 
    Variable eP : nat -> option Σp.
    Context {HeP : enumerator__T eP Σp}.

    Lemma term_model_card:
        same_cardinality Σ_f term.
    *)

(* 
   In the section, the Löwenheim–Skolem theorem downward part is shown 
   by henkin construction. We assume that the model M is non-empty and 
   classical, so this is basically a simple application of the model 
   existing Lemma.

   Result:
   ∀ M: model, ∃ N: model, M ≡ N and N is countable
*)
Section HenkinModel.
    (* Consider a nonempty classical model *)
    Variable M: model.
    Hypothesis classical_model: classical (interp' M).
    Hypothesis noempty: M.

    Definition input_theory: theory := theory_of_model M.

    Definition output_theory: theory := 
        Out_T (construct_construction (input_bot (closed_theory_of_model M))).

    (* Definition term_model M: model := 
    {|
        domain := term;
        interp' := model_bot (closed_theory_of_model M)
    |}. *)

    Lemma Hcon_in_M: consistent class input_theory.
    Proof.
        intros H. 
        enough (M ⊨[_] ⊥).
        exact (H0 (fun _ => noempty)).
        destruct H as [L [InL InCon]].
        intro rho; eapply sound_for_classical_model.
        exact classical_model. exact InCon.
        intros s h%(InL s).
        destruct h as [_ hpo]. 
        exact (hpo _).
    Qed.
    (* By Soundness of classical model *)

    Corollary Hcon_out_M: consistent class output_theory.
    Proof.
        intro H; apply Hcon_in_M.
        apply Out_T_econsistent with 
        (construct_construction (input_bot (closed_theory_of_model _))); assumption.
    Qed.

    Lemma classical_model': forall p φ, (M ⊨[p] ((¬ ¬ φ) → φ)).
    Proof.
        intros; cbn.
        intros; cbn; intros.
        apply classical_model with ⊥.
        intro; exfalso.
        now apply H.
    Qed.
    (* A classical proof :) *)

    Lemma contain_out_in:
        forall phi, closed phi -> 
            phi ∈ output_theory -> phi ∈ input_theory.
    Proof.
        intros φ closed_φ H.
        split. { assumption. }
        intro p.
        apply classical_model'; intros nphisat.
        assert (¬ φ ∈ output_theory).
        assert (closed (¬ φ)).
        constructor; eauto; constructor.
        apply Out_T_sub; split; eauto.
        intro p'; apply (sat_closed _ p p').
        all: try easy.
        apply Hcon_out_M.
        exists [φ; ¬ φ]; split.
        intros phi [<-|[<-|]]; easy.
        eapply IE with (phi := φ).
        eapply Ctx; right. now left.
        eapply Ctx; now left.
    Qed.

    (*  For any noempty and classical model M, there exists a countable term
        model which is elementary equivalence to M, whenever the signature is 
        at most countable. 
    *)
    Lemma countable_model: 
        exists N : interp term, M ≡ (Build_model N).
    Proof.
        exists (model_bot (closed_theory_of_model M)).
        split; intros.
        - apply (sat_closed _ p var). { assumption. }
          apply valid_T_model_bot. apply Hcon_in_M.
          unfold "∈", theory_of_model; eauto.
        - apply contain_out_in. { assumption. }
          setoid_rewrite <- subst_var.
          apply model_bot_correct.
          apply Hcon_in_M.
          eauto.
    Qed.

End HenkinModel.

(* 
    In this section, a stronger version of the Löwenheim–Skolem theorem downward part
    is shown based on the model satisfying the witness property, and the elementary 
    embedding from the henkin model to the original model is constructible.

   Result:
   ∀ M: model, M satisfy the witness property → ∃ N: model, N ⪳ M and N is countable.
*)

Section TermModel.

    Definition closed_term t := bounded_t 0 t.
    Existing Instance falsity_on.  

    Variable M: model.
    Variable h: nat -> M.

    Definition morphism: term -> M := eval M interp' h.
    Definition theory_under h: theory :=
        fun phi => M ⊨[h] phi.
    
    Definition interp_term: interp term :=
        {| i_func := func; i_atom := fun P v => atom P v ∈ theory_under h|}.
    Definition N: model :=
        {| domain := term; interp' := interp_term |}.

    Lemma eval_eval (ρ: env term) (t: term):
        (t ₜ[N] ρ) ₜ[M] h =
                 t ₜ[M] (fun x => (ρ x) ₜ[M] h).
    Proof.
          induction t; try easy; cbn.
          apply f_equal; rewrite map_map; apply map_ext_in.
          now apply IH.
    Qed.

    Lemma map_eval_eval (ρ: env term) {n} (v: t term n):
            map (fun t => (t ₜ[N] ρ) ₜ[M] h) v =
            map (fun t => t ₜ[M] (fun x => (ρ x) ₜ[M] h)) v.
    Proof.
        apply map_ext, eval_eval.
    Qed.

    Lemma eval_var t: t ₜ[N] var = t.
    Proof.
        induction t; cbn. easy.
        assert (map (eval term interp_term var) v = map (fun x => x) v).
        apply map_ext_in, IH.
        now rewrite H, map_id.
    Qed.

    Lemma term_subst_eval φ ξ: N ⊨[var] φ[ξ] <-> N ⊨[ξ] φ.
    Proof.
        rewrite (sat_comp (interp' N) var ξ φ).
        apply sat_ext.
        intro x; apply eval_var.
    Qed.

    Lemma term_subst_up φ ρ w:
        N ⊨[$w .: ρ] φ <-> N ⊨[$w..] φ[up ρ].
    Proof.
        rewrite <- term_subst_eval, <- (term_subst_eval φ[up ρ]).
        enough (φ[$w .: ρ] = φ[up ρ][$w..]) by now rewrite H.
        rewrite subst_comp; apply subst_ext.
        induction n; cbn. easy.
        unfold ">>"; rewrite subst_term_comp.
        now rewrite subst_term_id. 
    Qed.

    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.

    Section TarskiVaughtTest.

    Definition Henkin_env :=
        forall phi, exists w: nat, M ⊨[h w.:h] phi -> M ⊨[h] ∀ phi.

    Definition Henkin_env_blurred :=
        forall phi, (forall n, M ⊨[h n .: h] phi) -> M ⊨[h] ∀ phi. 

    Lemma Henkin_elementary_submodel: 
        Henkin_env -> exists (N: model), a_coutable_model N /\ N ⪳ M.
    Proof.
        intro fix_h. exists N. split. {apply term_model_countable. }
        exists morphism. intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            destruct (@fix_h (φ[up ρ])) as [wit h_prop].
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            assert(M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[h wit .: (var >> morphism)] φ[up ρ]).
            apply sat_ext; induction x; cbn; easy.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
    Qed.

    Lemma Henkin_blurred_elementary_submodel: 
        Henkin_env_blurred -> exists (N: model), a_coutable_model N /\ N ⪳ M.
    Proof.
        intro fix_h. exists N. split. {apply term_model_countable. }
        exists morphism. intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            specialize (@fix_h (φ[up ρ])) as h_prop.
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            intro wit.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            assert(M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[h wit .: (var >> morphism)] φ[up ρ]).
            apply sat_ext; induction x; cbn; easy.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
    Qed.


    Section help_verion.

    Lemma Henkin_elementary_submodel': 
        Henkin_env -> exists (N: model), N ⪳ M.
    Proof.
        intro fix_h. exists N. 
        exists morphism. intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            destruct (@fix_h (φ[up ρ])) as [wit h_prop].
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            assert(M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[h wit .: (var >> morphism)] φ[up ρ]).
            apply sat_ext; induction x; cbn; easy.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
    Qed.

    Lemma Henkin_blurred_elementary_submodel': 
        Henkin_env_blurred -> exists (N: model), N ⪳ M.
    Proof.
        intro fix_h. exists N.
        exists morphism. intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q. split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            specialize (@fix_h (φ[up ρ])) as h_prop.
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            intro wit.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            assert(M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[h wit .: (var >> morphism)] φ[up ρ]).
            apply sat_ext; induction x; cbn; easy.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
    Qed.

    Variable root: env M.
    Hypothesis root_in_h:
        forall x, exists y, root x = h y.

    Lemma Henkin_elementary_submodel_with_root: 
        Henkin_env -> exists (N: model) (mor: N -> M), N ⪳[mor] M /\ forall i, exists n, root i = mor n.
    Proof.
        intro fix_h. exists N. 
        exists morphism; split. intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            destruct (@fix_h (φ[up ρ])) as [wit h_prop].
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            assert(M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[h wit .: (var >> morphism)] φ[up ρ]).
            apply sat_ext; induction x; cbn; easy.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
        - intro i; unfold morphism.
          destruct (root_in_h i) as [w Hw].
          now exists ($ w); cbn. 
    Qed.

    End help_verion.

    End TarskiVaughtTest.

    Section WitnessProperty.

    (* which satify the witness property *)

    Definition witness_prop (M: model) := 
         forall phi, exists w, M ⊨[_] ((phi [w..]) → ∀ phi) /\ closed_term w. 

    Lemma elementary_syntatic_model: 
        witness_prop M -> exists (N: model) (mor: N -> M),
            a_coutable_model N /\ N ⪳[mor] M /\ forall i, exists n, h i = mor n.
    Proof.
        intro witness_prop_.
        exists N, morphism. split. {apply term_model_countable. } split. intros φ.
        induction φ using form_ind_falsity; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; intuition auto with *.
        - destruct q; split.
          + intros H d; destruct (Hphi φ) as [i phi].
            destruct (witness_prop_ φ) as [wit__i [witness_prop__i witness_closed]].
            eapply IHφ in H.
            eapply witness_prop__i.
            revert H; setoid_rewrite sat_comp; cbn.
            eapply sat_ext; induction x; cbn. 2: trivial.
            now apply bounded_eval_t with 0, witness_closed.
          + intros H d; rewrite (IHφ (d.:ρ)).
            specialize (H (morphism d)).
            revert H; apply sat_ext.
            induction x; easy.
        - intro i; now exists ($ i). 
    Qed.

    End WitnessProperty.

End TermModel.


(* Result of Henkin Model *)

Section WitnessPropertyLS.

    (* Consider a countable signature, and a function enumerate all formulas *)

    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.

    Theorem witness_property_LS: 
        forall M: model, witness_prop M -> inhabited M ->
            exists N: model, a_coutable_model N /\ N ⪳ M.
    Proof.
        intros M H [m].
        destruct (elementary_syntatic_model (fun _ => m) Hphi H) as (N & h & HN1 & HN2 &_).
        exists N; eauto.
    Qed.

    Corollary witness_property_LS_with_root: 
        forall M: model, witness_prop M  -> 
            forall m: M, exists (N: model), a_coutable_model N /\ 
                (exists h: N -> M, N ⪳[h] M /\ exists n: N, h n = m).
    Proof.
        intros M wit m.
        destruct (@elementary_syntatic_model M (fun _ => m) phi_ Hphi wit) as (N & h & C__N & P & index).
        exists N; split; eauto.
        exists h; split; eauto.
        destruct (index O) as [x R].
        now exists x. 
    Qed.

    End WitnessPropertyLS.

    Section CompletenessLS.

    Theorem completeness_LS: 
        forall M: model, (classical (interp' M)) -> inhabited M -> 
            exists N : interp term, M ≡ (Build_model N).
    Proof. intros M H []; apply countable_model; eauto. Qed.

    End CompletenessLS.

End TermIsCountable.














