Require Import FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
From Stdlib Require Import Program.Equality Vector.
Import VectorNotations.

(** Trivial Proof of Upward Löwenhim-Skolem Theorem *)

Section upward.

    Variables (N: Type) (n: N).
    Context (Σf : funcs_signature) (Σp : preds_signature).
    Variable model: interp N.

    Variable AnyCard: Type.

    Definition copy_to_M n: N + AnyCard := inl n.

    Definition copy_of_M (m: N + AnyCard)  :=
        match m with 
        | inl n => n 
        | inr _ => n
        end.

    Instance model_M: interp (N + AnyCard) := {
        i_func := fun F v => copy_to_M (i_func (map copy_of_M v));
        i_atom := fun P v => i_atom (map copy_of_M v)
    }.

    Fact pred_equal {X: Type} (P: X -> Prop) (x y: X):
        x = y -> P x <-> P y.
    Proof.
        now intros ->.
    Qed.

    Fact eval_first {X Y} (f: env X) (g: X -> Y) x i:
        ((x .: f) >> g) i = (g x .: (f >> g)) i.
    Proof.
        induction i; easy.
    Qed.

    Definition elim_dup (m: N + AnyCard) : N + AnyCard :=
        match m with
        | inl n => inl n 
        | inr _ => inl n 
        end.

    Lemma double_elim_dup (f: env (N + AnyCard)) x:
        forall i, ((x .: f >> elim_dup) >> elim_dup) i = ((x .: f) >> elim_dup) i.
    Proof.
        unfold ">>". destruct i; cbn. easy.
        now destruct (f i); cbn.
    Qed.    

    Fact elim_dup_M `{ff: falsity_flag} (ρ: env (N + AnyCard)) φ :
        ρ ⊨ φ <-> (ρ >> elim_dup) ⊨ φ.
    Proof.
        revert ρ; induction φ; cbn; intro ρ; try easy.
        + rewrite !map_map. apply pred_equal. 
          apply map_ext. induction a; cbn.
          unfold ">>". destruct (ρ x); easy.
          f_equal. 
          induction v; cbn. easy.
          f_equal. apply IH. constructor.
          apply IHv. intros. apply IH. now constructor. 
        + destruct b0; firstorder. 
        + destruct q; split; intro H.
          * intros [|]. specialize (H (inl n0)). 
            rewrite IHφ in H. 
            revert H. apply sat_ext; induction x; cbn; easy.
            specialize (H (inr a)).
            rewrite IHφ in H.
            rewrite IHφ.
            revert H; apply sat_ext; intro x; now rewrite double_elim_dup.
          * intros [|]; rewrite IHφ.
            specialize (H (inl n0)).
            revert H. apply sat_ext; induction x; cbn; easy.
            specialize (H (inl n)).
            revert H. apply sat_ext; induction x; easy.
          * destruct H as [[|] Hd].
            exists (inl n0). rewrite IHφ in Hd.
            revert Hd. apply sat_ext. induction x; easy.
            exists (inl n). rewrite IHφ in Hd.
            revert Hd. apply sat_ext. induction x; easy.
          * destruct H as [[|] Hd].
            exists (inl n0). rewrite IHφ.
            revert Hd. apply sat_ext. induction x; easy.
            exists (inl n). rewrite IHφ in Hd.
            rewrite IHφ.
            revert Hd. apply sat_ext; intro x. rewrite double_elim_dup.
            unfold ">>". now induction x; cbn. 
    Qed.

    Fact eq_inr_n `{ff: falsity_flag} i ρ φ :
        (inr i .: ρ >> copy_to_M) ⊨ φ <-> (inl n .: ρ >> copy_to_M) ⊨ φ.
    Proof.
        rewrite (elim_dup_M (inr i .: ρ >> copy_to_M) φ).
        apply sat_ext. unfold ">>". now destruct x; [easy|cbn].
    Qed.

    Lemma Upward:
        forall (ρ: env N) φ, 
            ρ ⊨ φ <-> (ρ >> copy_to_M) ⊨ φ.
    Proof.
        intros ρ φ.
        revert ρ; induction φ; cbn; intro ρ; try easy.
        + rewrite !map_map. apply pred_equal.
          apply map_ext. 
          induction a; cbn. easy.
          f_equal; induction v; cbn. easy.
          f_equal. apply IH; constructor.
          apply IHv; intros; apply IH; now constructor. 
        + destruct b0; cbn; firstorder. 
        + destruct q; cbn; split; intro H.
          * intros [n'|i'].
            destruct (IHφ (n'.:ρ)) as [H' _].
            specialize (H' (H n')); revert H'.
            apply sat_ext. induction x; easy.
            rewrite (eq_inr_n i' ρ φ).
            destruct (IHφ ( n.:ρ)) as [H' _].
            specialize (H' (H n)); revert H'.
            apply sat_ext'. induction x; easy.
          * intro d; rewrite (IHφ (d.:ρ)).
            specialize (H (copy_to_M d)).
            revert H. apply sat_ext'. induction x; easy.
          * destruct H as [d Hd].
            exists (copy_to_M d).
            rewrite IHφ in Hd.
            revert Hd. apply sat_ext'. induction x; easy.
          * destruct H as [[n'|i'] Hi].
            exists n'. rewrite IHφ.
            revert Hi. apply sat_ext'.
            induction x; cbn; easy. 
            exists n. rewrite IHφ.
            revert Hi. rewrite eq_inr_n.
            apply sat_ext. induction x; cbn; easy.
    Qed.

End upward.




