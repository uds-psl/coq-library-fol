Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.LogicalPrinciples.
Require Import FOL.ModelTheory.DCPre.
Require Import FOL.ModelTheory.ConstructiveLS.
From Stdlib Require Import Arith Cantor Lia PeanoNat Peano_dec.

Definition π__1 n := fst (of_nat n).
Definition π__2 n := snd (of_nat n).
Definition encode n m := to_nat (n, m).

Lemma cantor_left:
  forall x y, π__1 (encode x y) = x.
Proof.
  intros x y; unfold encode, π__1.
  now rewrite cancel_of_to.
Qed.

Definition cantor_right:
  forall x y, (π__2 (encode x y)) = y.
Proof.
  intros x y; unfold encode, π__2.
  now rewrite cancel_of_to.
Qed.

Opaque encode.


(** * Construction of Henkin Environments *)

Section Incl_im.
    Variables A B C: Type.
    Definition im_sub (ρ: A -> C) (ρ': B -> C)  := forall x, exists y, ρ x = ρ' y.
    Definition im_sub_k (ρ: nat -> C) (ρ': B -> C)  k := forall x, x < k -> exists y, ρ x = ρ' y.
End Incl_im.

Notation "ρ ⊂ ρ'" := (im_sub ρ ρ') (at level 25).
Notation "ρ ⊂[ k ] ρ'" := (im_sub_k ρ ρ' k) (at level 25).

Section Incl_facts.

    Lemma bounded_cantor b:
        Σt E, forall x, x < b -> π__1 x < E.
    Proof.
        clear; strong induction b.
        specialize (H (pred b)).
        destruct b; [exists 0; intros; lia| ].
        destruct H as [Ep EP]; [lia |].
        destruct (lt_dec Ep ((π__1 b))); 
        exists (S (π__1 b)) + exists (S Ep); 
        intros x H'; destruct (lt_dec x b); specialize (EP x); 
        lia || now assert (x = b) as -> by lia; lia.
    Qed.

    Lemma refl_sub {A B} (e: A -> B): e ⊂ e.
    Proof.
        intros x.
        now exists x.
    Qed.

    Lemma trans_sub  {A B} (a b c: A -> B): a ⊂ b -> b ⊂ c -> a ⊂ c.
    Proof.
        unfold "⊂"; intros.
        destruct (H x) as [ny H'], (H0 ny) as [my H''].
        exists my; congruence.
    Qed.

End Incl_facts.

Section FixedModel.
    Context {Σf : funcs_signature} {Σp : preds_signature} {M: model} {nonempty: M}. 

    (* Definition of Henkin condition *)
    Section Henkin_condition.
        Definition blurred_succ (ρ: env M) (ρ_s: env M) (φ: form): Prop :=
            ((forall n: nat, M ⊨[ρ_s n .: ρ] φ) -> M ⊨[ρ] (∀ φ)) 
                /\ 
            (M ⊨[ρ] (∃ φ) -> exists m, M ⊨[ρ_s m .: ρ] φ).

        Definition succ (ρ ρ_s: env M) φ := 
            (exists w, M ⊨[ρ_s w .: ρ] φ -> M ⊨[ρ] (∀ φ))
                /\
            (exists w, M ⊨[ρ] (∃ φ) -> M ⊨[ρ_s w .: ρ] φ).
 
    End Henkin_condition.

    Notation "ρ ⇒ ρ_s" := (forall φ, blurred_succ ρ ρ_s φ) (at level 25).
    Notation "ρ ⇒[ phi ] ρ_s" := (blurred_succ ρ ρ_s phi) (at level 25).

    Notation "ρ ⇒' ρ_s" := (forall φ, succ ρ ρ_s φ) (at level 25).
    Notation "ρ ⇒'[ phi ] ρ_s" := (succ ρ ρ_s phi) (at level 25).

    (* Some technical lemmas about bounded *)
    Section TechnicalLemmas.

        Lemma map_eval_cons (ρ ρ': env M) w  {n} (v: vec term n): 
        (forall t : term, In t v -> t ₜ[ M] ρ' = t`[fun x : nat => $(S x)] ₜ[ M] (w .: ρ') ) -> 
            map (eval M interp' ρ') v = map (eval M interp' (w .: ρ')) (map (subst_term (fun x : nat => $(S x))) v).
        Proof.
            intro H.
            induction v; cbn. {constructor. }
            rewrite IHv, (H h); [easy|constructor|].
            intros t H'; apply H.
            now constructor.
        Qed.

        Lemma comp_cons (ρ ρ': env M) (σ: nat -> term) w:
            forall x, (σ >> eval M interp' ρ') x = (σ >> subst_term ↑) x ₜ[ M] (w .: ρ').
        Proof.
            unfold ">>".
            intro x; induction (σ x); cbn; try easy.
            now rewrite map_eval_cons with (w := w).
        Qed.

        Lemma im_bounded_sub (ρ ρ': env M) b:
            ρ ⊂[b] ρ' -> exists (ξ : nat -> nat), forall x, x < b -> (ρ x) = (ρ' (ξ x)).
        Proof.
            induction b; cbn; [intros |].
            - exists (fun _ => O); lia.
            - intros. destruct IHb as [ξ Pξ].
            intros x Hx; apply (H x); lia. 
            destruct (H b) as [w Hw]; [lia|].
            exists (fun i => if (eq_nat_dec i b) then w else (ξ i)).
            intros; destruct (eq_nat_dec x b) as [->| eH]; [easy|].
            eapply Pξ; lia.  
        Qed.

        Lemma im_bounded_sub_form ρ ρ' φ k: bounded k φ -> ρ ⊂[k] ρ' -> 
            exists σ, (M ⊨[ρ] φ <-> M ⊨[ρ'] φ[σ]) /\ (forall x, x < k -> (σ >> (eval M interp' ρ')) x = ρ x).
        Proof.
            intros H H'.
            destruct (@im_bounded_sub _ _ _ H') as [ξ Hξ].
            exists (fun x => $ (ξ x)); split.
            - rewrite sat_comp.  
            apply bound_ext with k. exact H.
            intros. cbn. now apply Hξ.
            -  cbn. intros x Hx. now rewrite Hξ.
        Qed.

        Lemma bounded_sub_impl_henkin_env ρ ρ' ρ_s: 
            ρ' ⇒ ρ_s -> forall φ k, bounded k φ -> ρ ⊂[k] ρ' -> ρ ⇒[φ] ρ_s.
        Proof.
            intros Rρ' φ k H Ink.
            assert (bounded k (∀ φ)) as HS.
            apply bounded_S_quant, (bounded_up H); lia.
            destruct (im_bounded_sub_form HS Ink ) as (σ & fH & EH).
            destruct (Rρ' (φ[up σ])) as [P _]. split.
            + intro Hp; rewrite fH. apply P; revert Hp.
            intros H' n'; rewrite sat_comp.
            unshelve eapply (bound_ext _ H). exact (ρ_s n' .: ρ). 
            intros n Ln. destruct n; cbn; [easy|]. rewrite <- EH.
            now rewrite (comp_cons ρ ρ' σ (ρ_s n')). lia. apply H'.
            + assert (bounded k (∃ φ)) as HS'. apply bounded_S_quant, (bounded_up H); lia.
            destruct (im_bounded_sub_form HS' Ink ) as (σ' & fH' & EH').
            specialize (Rρ' (φ[up σ'])) as [_ P']. rewrite fH'; intro Hp.
            destruct (P' Hp) as [w Hw]. apply P' in Hp. 
            exists w; revert Hw; rewrite sat_comp.
            apply (bound_ext _ H). intros x HL.
            induction x; cbn. easy. rewrite <- EH'.
            now rewrite (comp_cons ρ ρ' σ' (ρ_s w)). lia.
        Qed.

        Lemma bounded_sub_impl_henkin_env' ρ ρ' ρ_s: 
        ρ' ⇒' ρ_s -> (forall φ k, bounded k φ -> ρ ⊂[k] ρ' -> ρ ⇒'[φ] ρ_s).
    Proof.
        intros Rρ' φ k H Ink.
        assert (bounded k (∀ φ)) as HS.
        apply bounded_S_quant.
        apply (bounded_up H); lia.
        destruct (im_bounded_sub_form HS Ink ) as (σ & fH & EH).
        destruct (Rρ' (φ[up σ])) as [[ws P] [ws1 P1]]. split.
        - exists ws. intro Hp; rewrite fH. 
          apply P; revert Hp.
          rewrite sat_comp.
          apply (bound_ext _ H); 
          intros n Ln. destruct n; cbn; [easy|]. rewrite <- EH.
          now rewrite (comp_cons ρ ρ' σ (ρ_s ws)). lia.
        - assert (bounded k (∃ φ)) as HS'. apply bounded_S_quant, (bounded_up H); lia.
          destruct (im_bounded_sub_form HS' Ink ) as (σ' & fH' & EH').
          specialize (Rρ' (φ[up σ'])) as [_ [v Pv]].
          exists v. rewrite fH'; intro Hp.
          apply Pv in Hp.  
          revert Hp; rewrite sat_comp.
          apply (bound_ext _ H). intros x HL.
          induction x; cbn. easy. rewrite <- EH'.
          now rewrite (comp_cons ρ ρ' σ' (ρ_s v)). lia.
    Qed.  

    Lemma incl_impl_wit_env ρ ρ' ρ_s: 
        ρ' ⇒ ρ_s -> ρ ⊂ ρ' -> ρ ⇒ ρ_s.
    Proof.
        intros H IN φ.
        destruct (find_bounded φ) as [k Hk].
        apply (@bounded_sub_impl_henkin_env ρ ρ' ρ_s H φ k Hk).
        intros x _; apply IN.
    Qed.

    Lemma incl_impl_wit_env' ρ ρ' ρ_s:
        ρ' ⇒' ρ_s -> ρ ⊂ ρ' -> ρ ⇒' ρ_s.
    Proof.
        intros H IN φ.
        destruct (find_bounded φ) as [k Hk].
        apply (@bounded_sub_impl_henkin_env' ρ ρ' ρ_s H φ k Hk).
        intros x _; apply IN.
    Qed.

    End TechnicalLemmas.

    (* Some facts about merging two countable set *)
    Section Merge.
        Definition merge {A: Type} (f1 f2: nat -> A): nat -> A :=
            fun n => match EO_dec n with 
                | inl L => f1 (projT1 L)
                | inr R => f2 (projT1 R)
            end.
        
        Fact merge_even {A: Type} (f1 f2: nat -> A):
            forall n, (merge f1 f2) (2 * n) = f1 n. 
        Proof.
            intros n. 
            unfold merge.
            destruct (EO_dec (2*n)).
            f_equal. destruct e. cbn; lia.
            destruct o. lia.
        Qed.
        
        Fact merge_odd {A: Type} (f1 f2: nat -> A):
            forall n, (merge f1 f2) (2 * n + 1) = f2 n. 
        Proof.
            intros n. 
            unfold merge.
            destruct (EO_dec (2*n + 1)).
            destruct e. lia.
            f_equal. destruct o. cbn; lia.
        Qed.
        
        Fact merge_l: forall {A: Type} (f1 f2: nat -> A), (f1 ⊂ merge f1 f2).
        Proof.
            intros A f1 f2 x; exists (2*x).
            assert (even (2*x)) by (exists x; lia).
            unfold merge; destruct (EO_dec (2*x)).
            enough (pi1 e = x) as -> by easy; destruct e; cbn; lia.
            exfalso; apply (@EO_false (2*x)); split; easy.
        Qed.
        
        Fact merge_r: forall {A: Type} (f1 f2: nat -> A), (f2 ⊂ merge f1 f2).
        Proof.
            intros A f1 f2 x; exists (2*x + 1).
            assert (odd (2*x + 1)) by (exists x; lia).
            unfold merge; destruct (EO_dec (2*x + 1)).
            exfalso; apply (@EO_false (2*x + 1)); split; easy.
            enough (pi1 o = x) as -> by easy; destruct o; cbn; lia.
        Qed.
        
        Fact merge_ex: forall {A: Type} (f1 f2: nat -> A), 
            forall x, exists y, f1 y = merge f1 f2 x \/ f2 y = merge f1 f2 x.
        Proof.
            intros A f1 f2 x; unfold merge.
            destruct (EO_dec x) as [[i Hi]|[i Hi]]; now exists i; (left + right). 
        Qed.

    End Merge.

    Definition blurred_henkin_next A B := A ⇒ B /\ A ⊂ B.
    Definition henkin_next A B := A ⇒' B /\ A ⊂ B.

    Notation "A '~>' B" := (blurred_henkin_next A B) (at level 60).
    Notation "A '~>'' B" := (henkin_next A B) (at level 60).

    Section Next_env.
        Lemma trans_succ a b c:
        (a ~> b) -> (b ~> c) -> (a ~> c).
        Proof.
            intros [H1 S1] [H2 S2]; split; [intro φ| ].
            destruct (H1 φ) as [H11 H12], (H2 φ) as [H21 H22];
            split; intro H.
            - apply H11. intro n. destruct (S2 n) as [w ->]. apply H.
            - destruct (H12 H) as [w Hw].
            destruct (S2 w) as [w' Hw'].
            exists w'. rewrite <- Hw'; easy.
            - eapply (trans_sub S1 S2).
        Qed.

    End Next_env.
        (* This section shows that countable directed F implies a fixpoint of ~> *)
    Section total_fixpoint'.

        Variable Path: nat -> env M.
        Hypothesis HP: forall n, Path n ~>' Path (S n).

        Lemma mono_Path1 a b: Path a ⊆ Path (a + b) .
        Proof.
            induction b.
            - assert (a + 0 = a) as -> by lia; apply refl_sub.
            - assert (a + S b = S(a + b)) as -> by lia.
                eapply trans_sub. exact IHb. apply HP.
        Qed.

        Lemma mono_Path2 a b: a < b -> Path a ⊂ Path b.
        Proof.
            assert (a < b -> Σt c, a + c = b) .
            intro H; exists (b - a); lia.
            intro aLb.
            destruct (H aLb) as [c Pc].
            specialize (mono_Path1 a c).
            now rewrite Pc. 
        Qed.

        Definition ι': env M := fun x => Path (π__1 x) (π__2 x).

        Lemma ι_incl' n: Path n ⊂ ι'.
        Proof.
            intro x; exists (encode n x); cbn.
            unfold ι'. now rewrite cantor_left, cantor_right.
        Qed.

        Lemma ι_succ' n: Path n ⇒' ι'.
        Proof.
            intros; destruct (HP n) as [P _];
            destruct (P φ) as [[w1 H1] [w2 H2]];
            specialize (ι_incl' (S n)) as Pws.
            split.
            - destruct (Pws w1) as [w Hw].
              exists w; intros; apply H1. 
              now rewrite Hw.
            - destruct (Pws w2) as [w Hw].
              exists w. now rewrite <- Hw; intros H%H2.
        Qed.    

        Lemma bounded_sub' b: 
            exists E: nat, ι' ⊂[b] (Path E).
        Proof.
            destruct (bounded_cantor b) as [E PE].
            exists E; intros x H.
            unfold ι'.
            specialize (PE _ H).
            specialize (mono_Path2  PE) as H1.
            destruct (H1 (π__2 x)) as [w Hw].
            now exists w.
        Qed.

        Theorem ι_Fixed_point': ι' ⇒' ι'.
        Proof.
            intros.
            destruct (find_bounded φ) as [b bφ].
            destruct (bounded_sub' b) as [E P].
            unshelve eapply bounded_sub_impl_henkin_env'; [exact (Path E) |exact b|..]; try easy.
            apply ι_succ'.
        Qed.

    End total_fixpoint'.

    Section total_fixpoint.

        Variable Path: nat -> env M.
        Hypothesis HP: forall n, Path n ~> Path (S n).

        Lemma mono_Path' a b: Path a ⊆ Path (a + b) .
        Proof.
            induction b.
            - assert (a + 0 = a) as -> by lia; apply refl_sub.
            - assert (a + S b = S(a + b)) as -> by lia.
                eapply trans_sub. exact IHb. apply HP.
        Qed.

        Lemma mono_Path a b: a < b -> Path a ⊂ Path b.
        Proof.
            assert (a < b -> Σt c, a + c = b) .
            intro H; exists (b - a); lia.
            intro aLb.
            destruct (H aLb) as [c Pc].
            specialize (mono_Path' a c).
            now rewrite Pc. 
        Qed.

        Definition ι: env M := fun x => Path (π__1 x) (π__2 x).

        Lemma ι_incl n: Path n ⊂ ι.
        Proof.
            intro x; exists (encode n x); cbn.
            unfold ι. now rewrite cantor_left, cantor_right.
        Qed.

        Lemma ι_succ n: Path n ⇒ ι.
        Proof.
            split; intros; destruct (HP n) as [P _];
            destruct (P φ) as [H1 H2];
            specialize (ι_incl (S n)) as Pws.
            - apply H1.
              intro n'; destruct (Pws n') as [w ->]. 
              apply H.
            - destruct (H2 H) as [w Hw].
              destruct (Pws w) as [x ->] in Hw.
              now exists x.
        Qed.    

        Lemma bounded_sub b: 
            exists E: nat, ι ⊂[b] (Path E).
        Proof.
            destruct (bounded_cantor b) as [E PE].
            exists E; intros x H.
            unfold ι.
            specialize (PE _ H).
            specialize (mono_Path  PE) as H1.
            destruct (H1 (π__2 x)) as [w Hw].
            now exists w.
        Qed.

        Theorem ι_Fixed_point: ι ⇒ ι.
        Proof.
            intros.
            destruct (find_bounded φ) as [b bφ].
            destruct (bounded_sub b) as [E P].
            unshelve eapply bounded_sub_impl_henkin_env; [exact (Path E) |exact b|..]; try easy.
            apply (ι_succ E).
        Qed.

    End total_fixpoint.

    (* This section shows that countable directed F implies a fixpoint of ~> *)
    Section directed_fixpoint.

        Variable F: nat -> env M.
        Hypothesis F_hypo: forall x y, exists k,  F x ~> F k /\ F y ~> F k.

        (* Since ~> is a transitive relation *)
        Lemma domain: forall (l: list nat), exists k, 
            forall x, List.In x l -> F x ~> F k.
        Proof.
            intro l; induction l as [|a l [k Hk]].
            - exists 42. intros x [].
            - destruct (F_hypo a k) as [w [Haw Hkw]].
            exists w; intros x [<-|Hx].
            + apply Haw.
            + eapply trans_succ.
                now apply Hk. apply Hkw. 
        Qed.

        Definition γ: env M := fun x => F (π__1 x) (π__2 x).

        Import List ListNotations.

        Lemma γ_env_incl n: F n ⊂ γ.
        Proof.
            intro x; exists (encode n x); cbn.
            unfold γ. now rewrite cantor_left, cantor_right.
        Qed.

        Lemma γ_succ n: F n ⇒ γ.
        Proof.
            destruct (@domain [n]) as [k Hk].
            destruct (Hk n) as [Pk _].
            firstorder.
            intro phi; destruct (Pk phi) as [H1 H2].
            split; intro H.
            - apply H1. intro x; destruct (γ_env_incl k x) as [w ->]; apply H.
            - destruct (H2 H) as [w Hw]. destruct (γ_env_incl k w) as [w' Hw'].
            exists w'. now rewrite <- Hw'.
        Qed.    

        Fixpoint n_lsit n :=
            match n with
            | O => []
            | S n => n::n_lsit n
            end.

        Lemma In_n_list n:
            forall a, a < n <-> In a (n_lsit n).
        Proof.
            induction n; cbn.
            - lia.
            - intro x; split. 
            + intros Hx. 
                assert (x = n \/ x < n) as [->| H1] by lia.
                now constructor. right. apply IHn; lia.
            + intros [->|H]; [lia|]. rewrite <- (IHn x) in H. lia.
        Qed.

        Lemma new_bounded b: 
            exists E: nat, γ ⊂[b] (F E).
        Proof.
            destruct (bounded_cantor b) as [E PE].
            destruct(@domain (n_lsit E)) as [K HK].
            exists K; intros x H. unfold γ.
            specialize (PE _ H).
            enough (In (π__1 x) (n_lsit E)) as H1.
            destruct (HK (π__1 x) H1) as [_ H3].
            exact (H3 (π__2 x)).
            now apply In_n_list.
        Qed.

        Theorem γ_Fixed_point: γ ⇒ γ.
        Proof.
            intros.
            destruct (find_bounded φ) as [b bφ].
            destruct (new_bounded b) as [E P].
            unshelve eapply bounded_sub_impl_henkin_env; [exact (F E) |exact b|..]; try easy.
            apply (γ_succ E).
        Qed.

    End directed_fixpoint.

    (* This section shows that ~>' is total *)
    Section dp_Next_env_total.

        Hypothesis dp: DP.
        Hypothesis ep: EP.
        Hypothesis cc : CC.
        Variable phi_ : nat -> form.
        Variable nth_ : form -> nat.
        Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

        Lemma CC_term: forall B (R: form -> B -> Prop), 
            B -> (forall x, exists y, R x y) -> 
                exists f: (form -> B),  forall n, R n (f n).
        Proof.
            intros B R b totalR.
            destruct (@cc B b (fun n => R (phi_ n))) as [g Pg]. 
            intro x. apply (totalR (phi_ x)).
            unshelve eexists. intros f; exact (g (nth_ f)). 
            intro n. cbn. specialize (Pg (nth_ n)).
            rewrite Hphi in Pg. eauto. 
        Qed.

        Definition dp_universal_witness:
            forall ρ, exists (W: nat -> M), forall φ, exists w, M ⊨[W w.:ρ] φ -> M ⊨[ρ] ∀ φ.
        Proof.
            intros.
            destruct (@CC_term M (fun phi w => M ⊨[w .: ρ] phi -> M ⊨[ρ] (∀ phi)) nonempty) as [F PF].
            - intro φ; destruct (dp nonempty (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
              exists (w tt); intro Hx; cbn; apply Hw; now intros [].
            - exists (fun n: nat => F (phi_ n)).
              intro φ; specialize (PF φ).
              exists (nth_ φ); rewrite (Hphi φ). easy.
        Qed.

        Definition ep_existential_witness:
            forall ρ, exists (W: nat -> M), forall φ, exists w, M ⊨[ρ] (∃ φ) -> M ⊨[W w.:ρ] φ.
        Proof.
            intros.
            destruct (@CC_term M (fun phi w => M ⊨[ρ] (∃ phi) -> M ⊨[w .: ρ] phi) nonempty) as [F PF].
            - intro φ; destruct (ep nonempty (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
              exists (w tt). intros Hx%Hw. now destruct Hx as [[] Hx].
            - exists (fun n: nat => F (phi_ n)).
              intro φ; specialize (PF φ).
              exists (nth_ φ); rewrite (Hphi φ). easy.
        Qed.

        Lemma dp_Henkin_witness:
            forall ρ, exists (W: nat -> M), ρ ⇒' W.
        Proof.
            intros ρ.
            destruct (dp_universal_witness ρ) as [Uw PUw].
            destruct (ep_existential_witness ρ) as [Ew PEw].
            exists (merge Uw Ew); intros φ; split.
            - destruct (PUw φ) as [w Pw].
              exists (to_merge_l w); intro H'; apply Pw.
              now  rewrite merge_even in H'.
            - destruct (PEw φ) as [w Pw].
              exists (to_merge_r w); intros H'.
              rewrite merge_odd. eauto.
        Qed.

        Lemma dp_Next_env:
            forall ρ, exists ρ', ρ ~>' ρ'.
        Proof.
            intros ρ.
            destruct (dp_Henkin_witness ρ) as [W' HW].
            exists (merge W' ρ); split.
            - intros φ; destruct (HW φ) as [[w1 H1] [w2 H2]]; split.
            exists (to_merge_l w1). rewrite merge_even. eauto.
            exists (to_merge_l w2). rewrite merge_even. eauto.
            - apply merge_r.
        Qed.

    End dp_Next_env_total.

        (* This section shows that ~> is total *)
    Section bdp_Next_env_total.
        Hypothesis bdp: BDP.
        Hypothesis bep: BEP.
        Hypothesis bcc : BCC.
        Variable phi_ : nat -> form.
        Variable nth_ : form -> nat.
        Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

        Lemma BCC_term: forall B (R: form -> B -> Prop), 
            B -> (forall x, exists y, R x y) -> 
                exists f: (nat -> B),  forall n, exists w, R n (f w).
        Proof.
            intros B R b totalR.
            destruct (@bcc B b (fun n => R (phi_ n))) as [g Pg].
            intro x. apply (totalR (phi_ x)).
            exists g. intro n. 
            specialize (Pg (nth_ n)).
            now rewrite Hphi in Pg.
        Qed.

        Definition universal_witness:
            forall ρ, exists (W: nat -> M), forall φ, (forall w, M ⊨[W w.:ρ] φ) -> M ⊨[ρ] ∀ φ.
        Proof.
            intros ρ.
            destruct (@BCC_term (nat -> M) (fun phi h => (forall w, M ⊨[(h w) .: ρ] phi) -> M ⊨[ρ] (∀ phi))) as [F PF].
            { exact (fun n => nonempty). }
            - intro φ; destruct (bdp (ρ (nth_ φ))(fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
            exists w; intro Hx; cbn; now apply Hw.
            - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
            intro φ; specialize (PF φ).
            intro H'. destruct PF as [n PF]; apply PF.
            intro w. specialize (H' (encode n w)).
            now rewrite cantor_left, cantor_right in H'.
        Qed.

        Definition existential_witness:
            forall ρ, exists (W: nat -> M), forall φ, M ⊨[ρ] (∃ φ) -> (exists w, M ⊨[W w.:ρ] φ).
        Proof.
            intros ρ.
            destruct (@BCC_term (nat -> M) (fun phi h =>  M ⊨[ρ] (∃ phi) -> (exists w, M ⊨[(h w) .: ρ] phi))) as [F PF].
            { exact (fun n => nonempty). }
            - intro φ; destruct (bep (ρ 0) (fun w => (M ⊨[w.:ρ] φ ))) as [w Hw].
            exists w; intro Hx; cbn; now apply Hw.
            - exists (fun (n: nat) => F (π__1 n) (π__2 n)).
            intro φ; specialize (PF φ).
            intro H'. destruct PF as [n PF]. 
            destruct (PF H') as [w Pw].
            exists (encode n w).
            now rewrite cantor_left, cantor_right.
        Qed.

        Lemma Henkin_witness:
            forall ρ, exists (W: nat -> M), ρ ⇒ W.
        Proof.
            intros ρ.
            destruct (universal_witness ρ) as [Uw PUw].
            destruct (existential_witness ρ) as [Ew PEw].
            exists (merge Uw Ew); intros φ; split; intro Hφ.
            - apply PUw; intro w.
            destruct (merge_l Uw Ew w) as [key ->].
            apply (Hφ key). 
            - destruct (PEw _ Hφ) as [w Pw].
            destruct (merge_r Uw Ew w) as [key Hk].
            exists key. now rewrite <- Hk.
        Qed.

        Lemma Next_env: forall ρ, exists ρ', (ρ ~> ρ').
        Proof.
            intros ρ.
            destruct (Henkin_witness ρ) as [W' HW].
            exists (merge W' ρ); split.
            - intros φ; destruct (HW φ) as [H1 H2]; split; intro Hφ.
            apply H1. intro n. specialize (Hφ (2 * n)).
            now rewrite merge_even in Hφ.
            destruct (H2 Hφ) as [w Hw].
            exists (2 * w). now rewrite merge_even.
            - apply merge_r.
        Qed.
    End bdp_Next_env_total.

    (* This section shows that ~> is directed *)
    Section Next_env_directed.
        Hypothesis bdp: BDP.
        Hypothesis bep: BEP.
        Hypothesis bcc : BCC.
        Variable phi_ : nat -> form.
        Variable nth_ : form -> nat.
        Hypothesis Hphi : forall phi,  phi_ (nth_ phi) = phi.

        Definition directed_Henkin_env: forall ρ1 ρ2, exists ρ, (ρ1 ~> ρ) /\ (ρ2 ~> ρ).
        Proof.
            intros ρ1 ρ2.
            pose (σ := merge ρ1 ρ2).
            destruct (Next_env bdp bep bcc Hphi σ) as [ρ [H1 H2]].
            exists ρ; split; split.
            + eapply incl_impl_wit_env. exact H1. apply merge_l.
            + eapply trans_sub. apply merge_l. apply H2.
            + eapply incl_impl_wit_env. exact H1. apply merge_r.
            + eapply trans_sub. apply merge_r. apply H2.
        Qed.
    End Next_env_directed.

End FixedModel.

Section Result.

    Theorem LS_downward_with_DC_LEM: 
       LEM -> DC -> DLS.
    Proof.
        intros LEM DC. apply LS_correct.
        intros Σ_f Σ_p C_Σ M m.
        destruct (enum_form C_Σ) as (phi_ & nth_ & Hphi).
        destruct (DC _ (fun n => m) (@henkin_next _ _ M)) as [F PF]; eauto.
        { intros A. unshelve eapply dp_Next_env; eauto.
          now rewrite DP_iff_LEM.
          now rewrite EP_iff_LEM.
          apply DC_impl_CC. now apply DC_impl_DC_root.
        }
        specialize (ι_Fixed_point' PF) as Succ.
        specialize Henkin_LS with (phi_ := phi_) (M := M) as [N [h Ph]].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        exists (ι F). 
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        exists N, h. eapply Ph.
    Qed.

    Theorem LS_downward_with_BDP_BEP_DC:
        BDP -> BEP -> DC -> DLS.
    Proof.
        intros BDP BEP DC. apply LS_correct.
        intros Σ_f Σ_p C_Σ M m.
        destruct (enum_form C_Σ) as (phi_ & nth_ & Hphi).
        assert (BCC: BCC). eapply BDC_impl_BCC.
        now apply DC_impl_BDC.
        destruct (DC _ (fun n => m) (@blurred_henkin_next _ _ M)) as [F PF]; eauto.
        { intros A. unshelve eapply Next_env; eauto. }
        pose (ι_Fixed_point PF) as Succ.
        specialize Blurred_Henkin_LS with (phi_ := phi_) (M := M) as [N [h Ph]].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        exists (ι F). 
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        exists N, h. eapply Ph.
    Qed.


    Theorem LS_downward:
        BDP -> BEP -> DDC -> BCC -> DLS.
    Proof.
        intros BDP BEP DDC BCC. apply LS_correct.
        intros Σ_f Σ_p C_Σ M m.
        destruct (enum_form C_Σ) as (phi_ & nth_ & Hphi).
        destruct (DDC _ (fun n => m) (@blurred_henkin_next _ _ M)) as [F PF]; eauto.
        { intros x y z Hx Hy. apply (trans_succ Hx Hy). }
        { intros A B. unshelve eapply directed_Henkin_env; eauto. }
        pose (γ_Fixed_point PF) as Succ.
        specialize Blurred_Henkin_LS with (phi_ := phi_) (M := M) as [N [h Ph]].
        { now intro phi; exists (nth_ phi); rewrite Hphi. }
        exists (γ F). 
        split; intros φ; [apply (Succ φ)| apply (Succ φ)].
        exists N, h. eapply Ph.
    Qed.

    Theorem LS_downward':  OBDC -> DLS.
    Proof.
        intros ? ? H_ H1. assert BDC2 as H2.
        {intros A a; eapply OBDC_impl_BDC2_on; eauto. }
        rewrite BDC2_iff_DDC_BCC in H2. destruct H2.
        eapply LS_downward; eauto.
        - intros A a. eapply (@OBDC_impl_BDP_on A); eauto.
        - intros A a. eapply (@OBDC_impl_BEP_on A); eauto.
    Qed.

End Result.



