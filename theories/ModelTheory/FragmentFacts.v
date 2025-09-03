
(*
  This section shows that isomorphism can imply elementary equivalence:
   M ≅ N → M ≡ N.
  Even in the function which is a relationship which M ≅ N → M ≅ᵣ N:
   M ≅ᵣ N → M ≡ N.
  Isomorphism can imply there exist a elementary embedding
   M ≅ N → M ⪳ N.

  Also, if there exist a elementary embedding from N to M, they're
  elementary equivalent.
   N ⪳ M → M ≡ N.

So we have the following pictorial representation:
         M ≅ᵣN ______   
        /            ∖  
  M ≅ N --- M ⪳ N --- M ≡ N
        \____________/

*)


Require Import FOL.ModelTheory.FragmentCore.
Require Import Coq.Program.Equality.
Local Set Implicit Arguments.


Section Iso_impl_elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Variables M N: model.

    Lemma term_preserved {ρ ρ'} (h: M -> N) :
          (forall x: nat, h (ρ x) = ρ' x)
        -> preserve_func h
        -> forall term: term, h (term ₜ[M] ρ) = term ₜ[N] ρ'.
    Proof.
        intros Heq pf.
        induction term; cbn. easy.
        rewrite <- (map_ext_in _ _ _ _ _ v IH).
        rewrite (pf _ (map (eval _ _ ρ) v)).
        now rewrite map_map.
    Qed.

    (*
        ∀ x, h (ρ x) = ρ' x
        func_preserved h
        ----------------------
        ∀ t, h (Ρ t) = Ρ' t
    *)

    Lemma iso_impl_elementary' (h: M -> N):
          isomorphism h
        -> forall φ ρ ρ', (forall x, h (ρ x) = ρ' x)
        -> M ⊨[ρ] φ <-> N ⊨[ρ'] φ.
    Proof.
        intros iso.
        induction φ; cbn; intros. { easy. }
        - rewrite (pred_strong_preserved (map (eval _ _ ρ) t)), map_map.
          now rewrite (map_ext _ _ _ _ (term_preserved H func_preserved)).
        - destruct b0. rewrite (IHφ1 _ _ H), (IHφ2 _ _ H). easy.
        - destruct q. split; intros hp d.
          + destruct (morphism_surjective d) as [m heq].
            apply (IHφ (m .: ρ) (d .: ρ')).
            induction x; cbn; easy.
            exact (hp m).
          + apply (IHφ (d .: ρ) (h d .: ρ')).
            induction x; cbn; easy.
            exact (hp (h d)).
    Qed.

    (*
        ∀ x, h (ρ x) = ρ' x
        M ⋍ N
        -------------------------
        ∀ φ, ρ ⊨ φ <-> ρ' ⊨ φ
    *)

    Arguments iso_impl_elementary' {_ _ _}.

    Theorem iso_impl_elementary: 
        M ≅ N -> M ≡ N.
    Proof.
        intros [h iso] phi cphi. split; try easy; intros asup env.
        - destruct (morphism_surjective (env O)) as [m _].
          apply (sat_closed _ _ (fun n => h m) cphi).
          now apply (iso_impl_elementary' (fun n => m) (fun n => h m)).
        - now apply (iso_impl_elementary' env (fun n => h (env n))).
    Qed.

End Iso_impl_elementary.


Section Basic_fact_Rel.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Variables M N: model.
    Variable R: M -> N -> Prop.

    Fact function_rel_map {X Y} (F: X -> Y -> Prop) {n: nat} (v1: vec X n) (v2 v2': vec Y n):
        function_rel F -> map_rel F v1 v2 -> map_rel F v1 v2' -> v2 = v2'.
    Proof.
        intros H1 H2.
        dependent induction H2; dependent destruction v2'; try easy.
        intros; specialize (IHmap_rel v2'); rewrite IHmap_rel.
        enough (y = h). rewrite H3; easy.
        dependent destruction H0.
        eapply H1. exact H. easy.
        dependent destruction H0; eassumption.
    Qed.

    Lemma In_rel_map {ρ ρ' n} (v: vec term n):
      (forall t : term, In t v -> R (t ₜ[ M] ρ) (t ₜ[ N] ρ'))
    -> map_rel R (map (eval M interp' ρ) v) (map (eval N interp' ρ') v).
    Proof.
      induction v; cbn; constructor.
      apply IHv; intros.
      all: apply H; now constructor.
    Qed.

    Lemma term_preserved_rel {ρ ρ'} (t: term) :
      (forall x: nat, R (ρ x) (ρ' x))
    -> isomorphism_rel R
    -> R (t ₜ[M] ρ) (t ₜ[N] ρ').
    Proof.
      induction t; intros; try easy.
      - apply H.
      - destruct (func_preserved_rel (map (eval _ interp' ρ) v)) as [v' [Hp Rvv']]; cbn.
        enough (v' = (map (eval _ interp' ρ') v)) as Heq.
        now rewrite <- Heq.
        eapply function_rel_map.
        destruct H0 as [_ _ [h _]].
        exact h. exact Rvv'.
        apply In_rel_map.
        intros; now apply IH.
    Qed.

    Lemma term_vec_preserved_rel {ρ ρ' n} (v: vec term n):
      (forall t: nat, R (ρ t) (ρ' t))
    -> isomorphism_rel R
    -> map_rel R (map (eval M interp' ρ) v) (map (eval N interp' ρ') v).
    Proof.
      induction v; cbn; constructor.
      now apply IHv.
      now apply term_preserved_rel.
    Qed.

    Lemma iso_impl_elementary_rel': isomorphism_rel R
    -> forall φ ρ ρ', (forall x, R (ρ x) (ρ' x))
    -> M ⊨[ρ] φ <-> N ⊨[ρ'] φ.
    Proof using ff.
      intros iso.
      induction φ; cbn; intros. { easy. }
    - destruct (pred_preserved_rel (map (eval _ interp' ρ) t)) as [v' [IH Rt]]; cbn.
      enough (v' = (map (eval _ interp' ρ') t)) as Heq.
      rewrite <- Heq; assumption.
      eapply function_rel_map.
      destruct iso as [_ _ [h _]]. exact h. exact Rt.
      apply term_vec_preserved_rel; eauto.
    - destruct b0. rewrite (IHφ1 _ _ H), (IHφ2 _ _ H). easy.
    - destruct q. split; intros hp d.
      + destruct morphism_biject_rel as [[fu total] [inj sur]].
        destruct (sur d) as [m Rmd].
        apply (IHφ (m .: ρ) (d .: ρ')).
        induction x; cbn. assumption.
        exact (H x). exact (hp m).
      + destruct morphism_biject_rel as [[fu total] [inj sur]].
        destruct (total d) as [n Rmn].
        apply (IHφ (d .: ρ) (n .: ρ')).
        induction x; cbn; eauto.
        exact (hp n).
    Qed.

  End Basic_fact_Rel.


  Section Rel_impl.

    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.
    Variables M N: model.

    Theorem iso_impl_iso_rel:
    M ≅ N -> M ≅ᵣ N.
    Proof.
      intros [h H]. exists (fun x y => h x = y); constructor.
      - intros phi v; exists (map h v); split.
        apply func_preserved. induction v; now constructor.
      - intros phi v; exists (map h v); split.
        apply pred_strong_preserved. induction v; now constructor.
      - specialize morphism_surjective as m;
        specialize morphism_injectived as i.
        split; split; eauto.
        intros x y y'. congruence.
        intros x. now exists (h x).
        intros x y y' A B; apply i; congruence.
    Qed.

    Theorem iso_impl_elementary_rel:
      M ≅ᵣ N -> M ≡ N.
    Proof.
      intros [h iso] phi cphi. split; try easy; intros asup env.
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (sur (env O)) as [m _].
      destruct (total m) as [n Rnm].
      apply (sat_closed _ _ (fun _ => n) cphi).
      now apply (@iso_impl_elementary_rel' _ _ _ _ _ _ iso phi (fun _ => m) (fun _ => n)).
    - destruct morphism_biject_rel as [[func total] [inj sur]].
      destruct (total (env O)) as [n _].
      destruct (sur n) as [m Rnm].
      apply (sat_closed _ _ (fun _ => m) cphi).
      now apply (@iso_impl_elementary_rel' _ _ _ _ _ _ iso phi  (fun _ => m) (fun _ => n)).
    Qed.

End Rel_impl.

Section el_emb_impl_elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Variables M N : model.
    Variable n: N.


  Theorem el_emb_impl_elementary:
    N ⪳ M -> M ≡ N.
  Proof.
    intros [h em] phi c__phi.
    split; firstorder.
    apply (sat_closed _ _ ((fun _ => n) >> h) c__phi).
    now apply em.
  Qed.

End el_emb_impl_elementary.


Section Basic_facts.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {b : falsity_flag}.

  Variables M N : model.

 Lemma cons_comp (f: M -> N) ρ d n:
   ((f d) .: ρ >> f) n = ((d.:ρ) >> f) n.
 Proof.
   induction n; try easy.
 Qed.

 Lemma cons_comp_sat (f: M -> N) ρ d phi:
    N ⊨[(f d) .: ρ >> f] phi <-> N ⊨[ (d .: ρ) >> f] phi.
 Proof.
  apply sat_ext, cons_comp.
 Qed.

 Lemma In_map (f: M -> N) p h {n} (v: vec term n):
   (forall t : term, In t v -> t ₜ[ N] (p >> h) = h (t ₜ[M] p))
  -> (map (eval N interp' (p >> h)) v = map h (map (eval M interp' p) v)).
Proof.
  induction v; cbn; try easy.
  intros; rewrite IHv, H; try constructor.
  now intros; eapply H; constructor.
Qed.

 Lemma map_eval_cons (f: M -> N) p {n} (v: vec term n):
   preserve_func f ->
   (map (eval N interp' (p >> f)) v =
   map f (map (eval M interp' p) v)).
 Proof.
   intro H; induction v; cbn; try easy.
   enough (h ₜ[N] (p >> f) = f (h ₜ[M] p)) as Heq by now rewrite IHv, Heq.
   induction h; try easy; cbn.
   now rewrite H; rewrite <- In_map. 
Qed.

 Lemma preserved_pred' (h: M -> N) P v:
    strong_preserve_pred h
 -> preserve_func h
 -> forall p, M ⊨[p] atom P v <-> N ⊨[p>>h] atom P v.
 Proof.
   split; cbn; intro.
   - specialize (H P (map (eval M interp' p) v)).
     apply H in H1; now rewrite map_eval_cons.
   - apply H; now rewrite <- map_eval_cons.
 Qed.

End Basic_facts.


Section iso_impl_el_emb.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {b : falsity_flag}.

  Variables M N : model.

 Theorem iso_impl_el_emb:
    M ≅ N -> M ⪳ N.
 Proof.
   intros [f iso]; exists f.
   intro phi. induction phi; try easy.
   - apply (preserved_pred' _ pred_strong_preserved func_preserved).
   - destruct b0; firstorder.
   - destruct q; cbn; split; intros.
     + destruct (morphism_surjective d) as [d' <-].
       now rewrite (cons_comp_sat f ρ d' phi), <- IHphi.
     + now rewrite IHphi, <- cons_comp_sat.
 Qed.

End iso_impl_el_emb.

Section trans_elem.

  Context {ff : falsity_flag}.

  Theorem trans_elem `{funcs_signature} `{preds_signature}
    (A B C: model): A ⪳ B -> B ⪳ C -> A ⪳ C.
  Proof.
    intros [h P] [g P']; exists (h>>g).
    intros phi ρ; now rewrite (P phi ρ), (P' phi).
  Qed.

End trans_elem.

