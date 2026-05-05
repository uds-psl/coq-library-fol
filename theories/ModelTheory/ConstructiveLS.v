Require Import Undecidability.FOL.Syntax.Asimpl.
Require Import FOL.ModelTheory.Core.
Local Set Implicit Arguments.

(** * Constructive Proofs of Löwenheim-Skolem Theorem *)

Section Henkin_Env.
    Context {Σf : funcs_signature} {Σp : preds_signature}.
    Existing Instance falsity_on.

    Definition closed_term t := bounded_t 0 t.
    Existing Instance falsity_on.  

    Variable M: model.
    Variable h: nat -> M.

    Definition morphism: term -> M := eval M interp' h.
    Definition theory_under h: theory :=
        fun phi => M ⊨[h] phi.
    
    Instance interp_term: interp term :=
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
        assert (map (eval _ _ var) v = map (fun x => x) v).
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
        N ⊨[w .: ρ] φ <-> N ⊨[w..] φ[up ρ].
    Proof.
        rewrite <- term_subst_eval, <- (term_subst_eval φ[up ρ]).
        enough (φ[w .: ρ] = φ[up ρ][w.:var]) by now rewrite H.
        rewrite subst_comp; apply subst_ext.
        induction n; cbn. easy.
        unfold ">>"; rewrite subst_term_comp.
        now rewrite subst_term_id. 
    Qed.

    Lemma term_subst_up' φ (ρ: nat -> term) w:
        M ⊨[w .: (ρ >> morphism)] φ -> M ⊨[w .: h] φ[up ρ].
    Proof.
        intros H.
        rewrite sat_comp.
        revert H. apply sat_ext'.
        induction x. easy.
        cbn. unfold ">>", morphism.
        rewrite <- (eval_up _ _ w). f_equal.
    Qed.

    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.

    Definition Henkin_env :=
        (forall phi, exists n, (M ⊨[h n .: h] phi) -> M ⊨[h] ∀ phi)
            /\
        (forall phi, exists m, M ⊨[h] (∃ phi) -> M ⊨[h m .: h] phi). 

    Theorem Henkin_env_el: 
        Henkin_env -> syntatic_model_on M.  
    Proof.
        intros [fix_h fix_h']. exists interp_term, morphism.
        intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; firstorder.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            specialize (@fix_h (φ[up ρ])) as [w h_prop].
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            cbn in H'; specialize (H' ($ w)).
            rewrite term_subst_up, H in H'.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
            + intros [wit Hwit].
            exists (eval _ interp' h wit).
            rewrite <- subst_var with φ.
            assert (M ⊨[ wit ₜ[ M] h .: ρ >> morphism] φ[var] <-> M ⊨[ (wit.:ρ) >> morphism] φ[var]).
            apply sat_ext.
            induction x; easy.
            rewrite H0.
            rewrite <- (H var (wit .: ρ)).
            now rewrite subst_var.
            + intros [w Hw]. 
            destruct (@fix_h' (φ[up ρ])) as [wit h_prop].
            exists ($ wit).
            rewrite term_subst_up, H.
            assert (M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[ h wit .: h] φ[up ρ]) as ->.
            apply sat_ext; induction x; easy.
            apply h_prop. 
            exists w.
            revert Hw. apply term_subst_up'.
    Qed.

    Definition Blurred_Henkin_env :=
        (forall phi, (forall n, M ⊨[h n .: h] phi) -> M ⊨[h] ∀ phi)
            /\
        (forall phi,  (M ⊨[h] (∃ phi) -> exists m, M ⊨[h m .: h] phi)). 

    Theorem Blurred_Henkin_env_el: 
        Blurred_Henkin_env -> syntatic_model_on M.  
    Proof.
        intros [fix_h fix_h']. exists interp_term, morphism.
        intros φ. induction φ using form_ind_subst; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; firstorder.
        - destruct q; split.
            + intros H'; destruct (Hphi (φ[up ρ])) as [i phi].
            specialize (@fix_h (φ[up ρ])) as h_prop.
            unfold morphism; rewrite <- sat_comp.
            apply h_prop.
            intro wit.
            cbn in H'; specialize (H' ($ wit)).
            rewrite term_subst_up, H in H'.
            now revert H'; apply sat_ext; induction x.
            + intros H' d. 
            rewrite <- subst_var with φ.
            rewrite (H var (d.:ρ)).
            specialize (H' (morphism d)).
            rewrite subst_var.
            revert H'; apply sat_ext.
            now induction x.
            + intros [wit Hwit].
            exists (eval _ interp' h wit).
            rewrite <- subst_var with φ.
            assert (M ⊨[ wit ₜ[ M] h .: ρ >> morphism] φ[var] <-> M ⊨[ (wit.:ρ) >> morphism] φ[var]).
            apply sat_ext.
            induction x; easy.
            rewrite H0.
            rewrite <- (H var (wit .: ρ)).
            now rewrite subst_var.
            + intros [w Hw]. 
            destruct (@fix_h' (φ[up ρ])) as [wit h_prop].
            exists w.
            revert Hw. apply term_subst_up'.
            exists ($ wit).
            rewrite term_subst_up, H.
            assert (M ⊨[ $wit.. >> morphism] φ[up ρ] <-> M ⊨[ h wit .: h] φ[up ρ]) as ->.
            apply sat_ext; induction x; easy.
            apply h_prop.
    Qed.

    Definition witness_prop (M: model) := 
        forall phi, 
            (exists w, M ⊨[_] ((phi [w..]) → ∀ phi) /\ closed_term w) 
            /\ 
            (exists w, M ⊨[_] ((∃ phi) → (phi [w..])) /\ closed_term w). 

    Lemma elementary_syntatic_model: 
        witness_prop M -> syntatic_model_on M.
    Proof.
        intro witness_prop_.
        exists interp_term, morphism.
        induction φ using form_ind_falsity; intro; try easy.
        - cbn; now rewrite map_map, map_eval_eval.
        - destruct b0; cbn; firstorder.
        - destruct q; split.
            + intros H d; destruct (Hphi φ) as [i phi].
            destruct (witness_prop_ φ) as [[wit__i [witness_prop__i witness_closed]] _].
            eapply IHφ in H.
            eapply witness_prop__i.
            revert H; setoid_rewrite sat_comp; cbn.
            eapply sat_ext; induction x; cbn. 2: trivial.
            now apply bounded_eval_t with 0, witness_closed.
            + intros H d; rewrite (IHφ (d.:ρ)).
            specialize (H (morphism d)).
            revert H; apply sat_ext.
            induction x; easy.
            + intros [wit Hwit]; destruct (Hphi φ) as [i phi].
            exists (eval _ interp' h wit); rewrite <- subst_var with φ.
            assert (M ⊨[ wit ₜ[ M] h .: ρ >> morphism] φ[var] <-> M ⊨[ (wit .:ρ) >> morphism] φ[var]) as ->.
            { apply sat_ext. induction x; easy. }
            rewrite subst_var. now rewrite <- IHφ.
            + destruct (witness_prop_  (φ[up ρ])) as [_ [wit__i [witness_prop__i witness_closed]]].
            intros [w Hw]. apply term_subst_up' in Hw.
            exists wit__i. rewrite IHφ.
            cbn in witness_prop__i.
            assert (M ⊨[h] φ[up ρ][wit__i..] -> M ⊨[ (wit__i.: ρ) >> morphism] φ) as H.
            {  asimpl. rewrite sat_comp. eapply sat_ext'. induction x; eauto. }
            apply H.
            eapply witness_prop__i. eauto.
    Qed.

End Henkin_Env.

Section HenkinLS.

    Context {Σf : funcs_signature} {Σp : preds_signature}.

    Variable phi_ : nat -> form.
    Hypothesis Hphi : forall phi, exists n, phi_ n = phi.

    Theorem WitnessProperty_LS:
        forall M: model, M -> witness_prop M -> syntatic_model_on M.
    Proof.
        intros M a HM.
        eapply elementary_syntatic_model; eauto.
    Qed.

    Theorem Henkin_LS: 
        forall M: model, (exists h: nat -> M, Henkin_env h) -> 
            syntatic_model_on M.
    Proof.
        intros M [h Hh].
        eapply Henkin_env_el; eauto.
    Qed.

    Theorem Blurred_Henkin_LS: 
        forall M: model, (exists h: nat -> M, Blurred_Henkin_env h) -> 
            syntatic_model_on M.
    Proof.
        intros M [h Hh].
        eapply Blurred_Henkin_env_el; eauto.
    Qed.

End HenkinLS.

