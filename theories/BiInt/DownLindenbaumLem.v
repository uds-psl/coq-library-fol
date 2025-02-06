Require Import FunctionalExtensionality.

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.
Require Import Arith.

Require Import existsT.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_logic.
Require Import FOBIH_properties.
Require Import FO_BiInt_Stand_Lindenbaum_lem.
Require Import FO_BiInt_Kripke_sem.

Section DownLind.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

(* Delete the following once we have the enumeration of formulas. *)

Variable form_enum : nat -> form.
Variable form_enum_sur : forall A, exists n, form_enum n = A.
Variable form_enum_unused : forall n, forall A m, form_enum m = A -> m <= n -> unused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.


Variable SLEM : forall P : Prop, P + ~ P.

Corollary LEM : forall P : Prop, P \/ ~ P.
Proof.
intro P ; destruct (SLEM P) ; auto.
Qed.


Notation "x 'el' L" := (List.In x L) (at level 70).
Notation "T |- phi" := (FOBIH_prv T phi) (at level 80).
Notation adj T phi := (fun psi => T psi \/ psi = phi).

Section DownLind_constr.

  Variable w : form -> Prop .
  Variable wex_henk : ex_henk w.


Lemma list_disj_subst_form l σ : (list_disj l)[σ] = list_disj (map (subst_form σ) l).
Proof.
induction l ; cbn ; auto.
apply f_equal ; auto.
Qed.

  Lemma Ldext_ex {L1 L2 psi} :
    ~ pair_der (Singleton _ (((∃ psi) ∧ list_conj L1) --< list_disj L2)) (Complement _ w)
    -> { c | w ((psi[$c..] ∧ list_conj L1) --< list_disj L2) }.
  Proof.
   intros HD.
   assert (w (∃ (psi ∧ (list_conj L1)[↑] --< (list_disj L2)[↑]))).
   - destruct (LEM (w (∃ psi ∧ (list_conj L1)[↑] --< (list_disj L2)[↑]))) ; auto.
     exfalso. apply HD. apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
     eapply dual_MP.
     + exists [] ; repeat split ; auto.
         * apply NoDup_nil.
         * intros B HB ; inversion HB.
         * cbn. apply Dual_Constant_Domain.
     + assert (pair_der (Singleton form (∃ psi ∧ (list_conj L1)[↑] --< (list_disj L2)[↑])) (Complement form w)).
        { exists [(∃ psi ∧ (list_conj L1)[↑] --< (list_disj L2)[↑])]. repeat split ; auto.
          - apply NoDup_cons. intro H0 ; inversion H0. apply NoDup_nil.
          - intros C HC ; inversion HC ; subst ; auto. inversion H0.
          - cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; apply In_singleton. }
     destruct H0 as (l & Hl0 & Hl1 & Hl2). exists (nodup (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) (list_disj L2 :: l)).
     repeat split ; auto.
        * apply NoDup_nodup.
        * intros C HC. apply nodup_In in HC. inversion HC ; subst. left ; split. right ; apply Hl1 ; auto.
        * apply list_disj_nodup. cbn. eapply FOBIH_subst in Hl2. Unshelve. 4: exact ↑. all: auto.
          apply FOBIH_monot with (Γ1:= Singleton _ ((∃ psi ∧ (list_conj L1)[↑] --< (list_disj L2)[↑])[↑])) in Hl2.
          -- cbn in Hl2.
              assert (Singleton form ((psi[up ↑] ∧ (list_conj L1)[↑][up ↑] --< (list_disj L2)[↑][up ↑])[$0..]) |- (list_disj l)[↑]).
              { apply MP with (∃ psi[up ↑] ∧ (list_conj L1)[↑][up ↑] --< (list_disj L2)[↑][up ↑]).
                - apply FOBIH_Deduction_Theorem. apply (FOBIH_monot _ _ Hl2).
                  intros C HC. right ; auto.
                - eapply MP. 2: apply Id ; apply In_singleton. apply Ax ; eapply QA3 ; reflexivity. }
              cbn in H0. rewrite !form_subst_help in H0.
              apply FOBIH_monot with (Γ:= Union _ (Empty_set _) (Singleton form (∃ psi ∧ (list_conj L1)[↑]))).
              ++ apply FOBIH_Detachment_Theorem. apply EC ; cbn.
                   apply FOBIH_Deduction_Theorem. apply FOBIH_monot with (Γ:= Singleton form (psi ∧ (list_conj L1)[↑])).
                   ** rewrite (list_disj_subst_form l). apply FOBIH_Dual_Detachment_Theorem. rewrite <- list_disj_subst_form. auto.
                   ** intros C HC ; inversion HC ; subst. right ; split.
              ++ intros C HC ; inversion HC ; subst ; auto. inversion H1.
          -- intros C HC ; destruct HC as (B & HB0 & HB1) ; subst. inversion HB1 ; subst. split.
    - apply wex_henk in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Qed.

  Lemma Ldext_all {L1 L2 psi} :
    ~ pair_der (Singleton _ ((list_conj L1 --< ∀ psi) --< list_disj L2)) (Complement _ w)
    -> { c | w ((list_conj L1 --< psi[$c..]) --< list_disj L2) }.
  Proof.
    intros HD.
    assert (w (∃ ((list_conj L1)[↑] --< psi) --< (list_disj L2)[↑])).
    - destruct (LEM (w (∃ ((list_conj L1)[↑] --< psi) --< (list_disj L2)[↑]))) ; auto.
      exfalso. apply HD.
      assert (pair_der (Singleton form (∃ ((list_conj L1)[↑] --< psi) --< (list_disj L2)[↑])) (Complement form w)).
      { exists [(∃ ((list_conj L1)[↑] --< psi) --< (list_disj L2)[↑])]. repeat split ; auto.
        + apply NoDup_cons. intro H0 ; inversion H0. apply NoDup_nil.
        + intros C HC ; inversion HC ; subst ; auto. inversion H0.
        + cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; apply In_singleton. }
      destruct H0 as (l & Hl0 & Hl1 & Hl2). exists l.
      repeat split ; auto.
      + apply FOBIH_Dual_Deduction_Theorem. eapply MP.
         * eapply MP.
            -- eapply MP.
                ++ apply Imp_trans.
                ++ apply imp_Id_gen.
            -- apply list_disj_app. eapply MP.
                ++ apply Thm_irrel.
                ++ apply FOBIH_Dual_Deduction_Theorem. eapply MP.
                     ** apply FOBIH_monot with (Γ:=Empty_set _).
                         --- apply Constant_Domain_Ax.
                         --- intros C HC ; inversion HC.
                     ** apply prv_AI. eapply FOBIH_subst in Hl2. Unshelve. 3: exact ↑. 2: exact ⊤.
                        apply FOBIH_monot with (Γ1:= Singleton _ ((∃ ((list_conj L1)[↑] --< psi) --< (list_disj L2)[↑])[↑])) in Hl2.
                        --- cbn in Hl2.
                             assert (Singleton form ((((list_conj L1)[↑][up ↑] --< psi[up ↑]) --< (list_disj L2)[↑][up ↑])[$0..]) |- (list_disj l)[↑]).
                             { apply MP with (∃ ((list_conj L1)[↑][up ↑] --< psi[up ↑]) --< (list_disj L2)[↑][up ↑]).
                                - apply FOBIH_Deduction_Theorem. apply (FOBIH_monot _ _ Hl2).
                                   intros C HC. right ; auto.
                                - eapply MP.
                                   * apply Ax ; eapply QA3 ; reflexivity.
                                   * apply Id ; apply In_singleton. }
                             cbn in H0. rewrite !form_subst_help in H0.
                             rewrite list_disj_subst_form.
                             apply FOBIH_monot with (Γ:= (Singleton form (list_conj L1)[↑])).
                             *** apply FOBIH_Dual_Detachment_Theorem. rewrite map_app. apply list_disj_app_distr.
                                  rewrite <- list_disj_subst_form. apply FOBIH_Dual_Detachment_Theorem. rewrite <- list_disj_subst_form ; auto.
                             *** intros C HC ; inversion HC ; subst. exists (list_conj L1) ; repeat split ; auto.
                        --- intros C HC ; destruct HC as (B & HB0 & HB1) ; inversion HB1 ; subst ; split.
         * apply prv_Top.
    - apply wex_henk in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Qed.


  Variable wall_henk : all_henk w.
  Variable wconsist : consist w.
  Variable wprime : prime w.
  Variable wded_clos : ded_clos w.
  Variable A0 B0 : form.

  Hypothesis w_nder : ~ (pair_der (Singleton _ A0) (fun x => (Complement _ w) x \/ x = B0)).

  Fixpoint Ldext (n : nat) : list form * list form :=
    match n with
    | 0 => ([A0], [B0])
    | S n => let (L1, L2) := Ldext n in let phi := form_enum n in
            match form_all phi, form_ex phi with
            | inl (exist _ psi _), _ => match SLEM (pair_der (Singleton _ ((list_conj L1 --< ∀ psi) --< list_disj L2)) (Complement _ w)) with
                                     | inl _ => (∀ psi :: L1, L2)
                                     | inr H => (L1, ∀ psi :: psi[$(proj1_sig (Ldext_all H))..] :: L2)
                                     end
            | _, inl (exist _ psi _) => match SLEM (pair_der (Singleton _ (((∃ psi) ∧ list_conj L1) --< list_disj L2)) (Complement _ w)) with
                                     | inl _ => (L1, ∃ psi :: L2)
                                     | inr H => (∃ psi :: psi[$(proj1_sig (Ldext_ex H))..] :: L1, L2)
                                     end
            | _, _ => if SLEM (pair_der (Singleton _ ((list_conj (phi :: L1)) --< list_disj L2)) (Complement _ w))
                     then (L1, phi :: L2) else (phi :: L1, L2)
            end
    end.

  Lemma Ldext_cum1 n n' :
    n <= n' -> incl (fst (Ldext n)) (fst (Ldext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Ldext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Ldext_cum2 n n' :
    n <= n' -> incl (snd (Ldext n)) (snd (Ldext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Ldext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Ldext_nder n :
    ~ (pair_der (Singleton _ (list_conj (fst (Ldext n)) --< list_disj (snd (Ldext n)))) (Complement _ w)).
  Proof.
    induction n; intros HD.
    - cbn in HD. apply w_nder.
      assert (adj (Complement form w) B0 = Union _ (Singleton _ B0) (Complement _ w)).
      apply Extensionality_Ensembles ; split ; intros A HA ; unfold In in *. destruct HA ; subst.
      right ; auto. left ; split. inversion HA ; subst ; auto. inversion H ; subst ; auto.
      rewrite H ; clear H. apply (@gen_FOBIH_Dual_Detachment_Theorem) ; auto.
      destruct HD as (l & Hl0 & Hl1 & Hl2). exists l ; repeat split ; auto.
      apply (FOBIH_comp _ _ Hl2). intros B HB ; inversion HB ; subst.
      apply FOBIH_monot with (Γ:= Union _ (Empty_set _) (Singleton form (A0 --< B0))).
      apply FOBIH_Detachment_Theorem. eapply MP. eapply MP. apply Imp_trans.
      apply monoL_Excl. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
      apply imp_Id_gen. apply EFQ. apply monoR_Excl.
      eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity. apply imp_Id_gen.
      apply FOBIH_Deduction_Theorem. apply prv_Top.
      intros C HC ; inversion HC ; subst ; auto. inversion H.
    - cbn in *. destruct Ldext, form_all as [[]|]; try destruct form_ex as [[]|] ;
        destruct SLEM; try destruct Ldext_all; try destruct Ldext_ex; subst; cbn in *.
      + apply IHn. apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in p ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in p ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in HD ; auto.
         apply (@Cut) with (∀ x) ; auto.
         destruct HD as (l' & Hl'0 & Hl'1 & Hl'2). exists l' ; repeat split ; auto.
         apply (FOBIH_comp _ _ Hl'2) ; auto. intros. inversion H ; subst. apply prv_CI ; apply Id.
         right ; split. left ; split.
         destruct p as (l' & Hl'0 & Hl'1 & Hl'2). exists l' ; repeat split ; auto.
         intros. apply Hl'1 in H. inversion H ; subst. inversion H0 ; subst. right ; split.
         inversion H0 ; subst. left ; auto. left ; right ; auto.
      + destruct HD as (l' & Hl'0 & Hl'1 & Hl'2).
         assert (w (list_disj l')). apply wded_clos. eapply MP. eapply MP. eapply MP. apply Imp_trans.
         apply FOBIH_monot with (Γ:= Empty_set _). apply monoR_Excl. apply monoL_Excl.
         eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
         apply Ax ; eapply QA2 ; reflexivity. apply imp_Id_gen. intros C HC ; inversion HC.
         2: apply Id ; exact w0.
         apply FOBIH_monot with (Γ:= Empty_set _). apply FOBIH_Deduction_Theorem.
         apply FOBIH_monot with (Γ:=Singleton form ((list_conj l --< (∀ x) ∨ x[$x0..]) --< list_disj l0)).
         apply FOBIH_Dual_Deduction_Theorem.
         apply FOBIH_monot with (Γ:=Union _ (Empty_set _) (Singleton form ((list_conj l --< (∀ x) ∨ x[$x0..])))).
         apply FOBIH_Detachment_Theorem. apply list_disj_app. apply FOBIH_Deduction_Theorem.
         apply FOBIH_monot with (Γ:=Singleton form ((list_conj l --< (∀ x) ∨ x[$x0..]))). apply FOBIH_Dual_Deduction_Theorem.
         apply FOBIH_Dual_Detachment_Theorem in Hl'2.
         apply (prv_DE _ _ _ _ Hl'2). apply (prv_DE _ (∀ x) (x[$x0..] ∨ list_disj l0)). apply Id ; right ; split.
         apply prv_DI1. apply prv_DI1. apply Id ; unfold In ; auto. apply (prv_DE _ x[$x0..] (list_disj l0)). apply Id ; right ; split.
         apply prv_DI1. apply prv_DI2 ; apply Id ; unfold In ; auto. apply prv_DI2. apply list_disj_app_distr.
         apply prv_DI1. apply Id ; unfold In ; auto. apply prv_DI2. apply list_disj_app_distr.  apply prv_DI2. apply Id ; unfold In ; auto.
         intros C HC ; inversion HC ; subst ; right ; auto. intros C HC ; inversion HC ; subst ; auto. inversion H.
         intros C HC ; inversion HC ; subst ; right ; auto. intros C HC ; inversion HC.
         apply list_disj_prime in H ; auto. destruct H as (B & HB0 & HB1). apply Hl'1 in HB0 ; auto.
      + apply IHn. apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in p ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in HD ; auto.
         apply (@Cut) with (∃ x) ; auto.
         destruct p as (l' & Hl'0 & Hl'1 & Hl'2). exists (nodup (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) (list_disj l0 :: l')) ; repeat split ; auto.
         apply NoDup_nodup. intros. apply nodup_In in H. inversion H ; subst. left ; split. apply Hl'1 in H0 ; auto.
         apply list_disj_nodup. cbn. apply prv_DI2. apply (@prv_cut _ _ eq_dec_preds eq_dec_funcs _ _ _ Hl'2). intros C HC ; inversion HC ; subst.
         apply prv_CI ; apply Id. right ; split. left ; split.
         apply (@Cut) with ((∃ x) ∨ list_disj l0) ; auto.
         exists [(∃ x) ; list_disj l0]. repeat split. apply NoDup_cons. intro. inversion H ; subst. destruct l0 ; cbn in H0 ; inversion H0.
         inversion H0. apply NoDup_cons. intro. inversion H. apply NoDup_nil.
         intros A HA ; inversion HA ; subst. right ; split. inversion H ; subst. left ; left ; split. inversion H0.
         cbn. eapply MP. apply Or_imp_assoc. apply Ax ; eapply A3 ; reflexivity. apply Id ; right ; split.
         destruct HD as (l' & Hl'0 & Hl'1 & Hl'2). exists l'. repeat split ; auto. intros A HA ; apply Hl'1 in HA ; inversion HA ; subst.
         inversion H ; subst. right ; split. left ; left ; right ; auto.
      + destruct HD as (l' & Hl'0 & Hl'1 & Hl'2).
         assert (w (list_disj l')). apply wded_clos. eapply MP. eapply MP. eapply MP. apply Imp_trans.
         apply FOBIH_monot with (Γ:= Empty_set _). apply monoR_Excl. 4: apply Id ; exact w0.
         apply FOBIH_Deduction_Theorem. apply prv_CI. eapply MP. apply Ax ; eapply QA3 ; reflexivity.
         apply prv_CE1 with (list_conj l). apply Id ; right ; split. apply prv_CI. apply prv_CE1 with (list_conj l).
         apply Id ; right ; split. apply prv_CE2 with (x[$x0..]). apply Id ; right ; split. intros A HA ; inversion HA.
         apply FOBIH_Deduction_Theorem. apply (FOBIH_monot _ _ Hl'2). intros A HA ; inversion HA ; subst ; right ; split.
         apply list_disj_prime in H ; auto. destruct H as (B & HB0 & HB1). apply Hl'1 in HB0 ; auto.
      + apply IHn. apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
         apply (@gen_FOBIH_Dual_Detachment_Theorem) in p ; auto.
         assert (pair_der (Union _ (Singleton _ (list_conj l)) (Singleton _ (form_enum n))) (Union _ (Singleton form (list_disj l0)) (Complement _ w))).
         destruct p as (l' & Hl'0 & Hl'1 & Hl'2). exists l' ; repeat split ; auto. apply (@prv_cut _ _ eq_dec_preds eq_dec_funcs _ _ _ Hl'2).
         intros C HC ; inversion HC ; subst. apply prv_CI. apply Id ; right ; split. apply Id ; left ; split.
         assert (pair_der (Singleton _ (list_conj l)) (Union _ (Union _ (Singleton _ (list_disj l0)) (Complement _ w)) (Singleton _ (form_enum n)))).
         destruct HD as (l' & Hl'0 & Hl'1 & Hl'2). exists (nodup (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) ((form_enum n) :: (list_disj l0) :: l')) ; repeat split ; auto.
         apply NoDup_nodup. intros A HA ; apply nodup_In in HA ; inversion HA ; subst. right ; split.
         inversion H0 ; subst. left ; left ; split. left ; right ; apply Hl'1 ; auto. apply list_disj_nodup.
         cbn. apply FOBIH_Dual_Detachment_Theorem in Hl'2. apply prv_DE with (form_enum n ∨ list_disj l0) (list_disj l') ; auto.
         apply prv_DE with (form_enum n) (list_disj l0). apply Id ; unfold In ; auto. apply prv_DI1. apply Id ; unfold In ; auto.
         apply prv_DI2 ; apply prv_DI1 ; apply Id ; unfold In ; auto. apply prv_DI2 ; apply prv_DI2 ; apply Id ; unfold In ; auto.
         apply (@Cut) with (form_enum n) ; auto.
      + auto.
  Qed.

  Lemma Ldext_A0 n :
    A0 el fst (Ldext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Ldext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

  Lemma Ldext_B0 n :
    B0 el snd (Ldext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Ldext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

 Definition dext phi := exists n, phi el fst (Ldext n).

  Lemma dext_der n :
    dext |- list_conj (fst (Ldext n)).
  Proof.
    apply prv_list_conj. intros A HA. apply prv_ctx. now exists n.
  Qed.

  Lemma dext_prv phi :
    dext |- phi -> exists n, (fun psi => psi el fst (Ldext n)) |- phi.
  Proof.
    intros [L[H1 H2]] % (@prv_compact _ _ eq_dec_preds eq_dec_funcs). revert phi H2.
    induction L as [|psi L IH]; intros phi H2.
    - exists 0. cbn. eapply prv_weak; try apply H2. intros B [].
    - destruct (H1 psi) as [k Hk]; try now left.
      destruct IH with (psi --> phi) as [n Hn].
        * intros B HB. apply H1. now right.
        * apply prv_DT. eapply prv_weak; try apply H2. unfold Included, In. cbn. intuition.
        * exists (n + k). apply prv_DT in Hn. eapply prv_weak; try apply Hn.
          intros B [| ->] ; eapply Ldext_cum1; try eassumption; lia.
  Qed.

  Lemma Ldext_mono T n n' :
    n <= n' -> T |- list_disj (snd (Ldext n)) -> T |- list_disj (snd (Ldext n')).
  Proof.
    intros H. apply list_disj_mono. now apply Ldext_cum2.
  Qed.

  Lemma  list_disj_weak : forall (T : form -> Prop) (L L' : list form),
  (forall A, A el L -> T |- A --> list_disj L') -> T |- list_disj L -> T |- list_disj L'.
  Proof.
  intros T L. revert T. induction L ; cbn ; auto.
  - intros. eapply MP. apply EFQ. auto.
  - intros. eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
    3: exact H0. apply H ; auto. apply FOBIH_Deduction_Theorem. apply IHL.
    intros. apply FOBIH_monot with T. apply H ; auto. intros C HC ; left ; auto.
    apply Id ; right ; split.
  Qed.

  Lemma dext_nder n :
    ~ (pair_der dext (Union _ (Singleton _ (list_disj (snd (Ldext n)))) (Complement _ w))).
  Proof.
    intros (l & Hl0 & Hl1 & Hl2). destruct (dext_prv _ Hl2) as (k & Hk).
    apply (Ldext_nder (max n k)). apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
    exists (nodup (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) ((list_disj (snd (Ldext (Init.Nat.max n k)))) :: remove (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) (list_disj (snd (Ldext n))) l)).
    repeat split ; auto. apply NoDup_nodup. intros A HA ; apply nodup_In in HA. inversion HA ; subst. left ; split.
    right. apply in_remove in H. destruct H. apply Hl1 in H. inversion H ; subst. exfalso ; inversion H1 ; subst ; auto. auto.
    apply list_disj_nodup. apply list_disj_weak with l.
    intros A HA. destruct ((@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) A (list_disj (snd (Ldext n)))) ; subst. apply FOBIH_Deduction_Theorem.
    eapply MP. apply Ax ; eapply A3 ; reflexivity. apply list_disj_mono with (snd (Ldext n)).
    apply Ldext_cum2. lia. apply Id ; right ; split. pose (Hl1 _ HA).
    inversion u ; subst. inversion H ; subst. exfalso ; auto. cbn. eapply MP. eapply MP. apply Imp_trans.
    2: apply Ax ; eapply A4 ; reflexivity. apply FOBIH_Deduction_Theorem. apply prv_list_disj with A.
    apply in_in_remove ; auto. apply Id ; right ; split. apply (@prv_cut _ _ eq_dec_preds eq_dec_funcs _ _ _ Hk). intros B HB.
    eapply MP. apply list_conj_in_list. apply (Ldext_cum1 k (max n k)) ; auto. lia. apply Id ; split.
  Qed.

  Lemma dext_el phi :
    dext phi -> w phi.
  Proof.
    intro H ; subst ; auto. destruct H.
    destruct (LEM (w phi)) ; auto. exfalso. eapply (dext_nder (S x)) ; auto.
    exists [phi]. repeat split.
    - apply NoDup_cons. intro H2 ; inversion H2. apply NoDup_nil.
    - intros D HD ; inversion HD ; subst. right ; auto. inversion H1.
    - cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id. exists x ; exact H.
  Qed.

  Lemma dext_ex_henk :
    ex_henk dext.
  Proof.
    intros phi H. remember (form_index (∃ phi)) as n.
    destruct (Ldext n) as [L1 L2] eqn: HL.
    destruct (SLEM (pair_der (Singleton _ (((∃ phi) ∧ list_conj L1) --< list_disj L2)) (Complement _ w))) eqn: HS.
    { exfalso. destruct H. assert (J: pair_der (Singleton form ((∃ phi) ∧ list_conj L1 --< list_disj L2)) (Complement form w)) ; auto.
      destruct J as (l & Hl0 & Hl1 & Hl2). apply FOBIH_Dual_Detachment_Theorem in Hl2.
      apply (@prv_cut _ _ eq_dec_preds eq_dec_funcs) with (T':=Union _ (Singleton form (∃ phi)) (Singleton form (list_conj L1))) in Hl2.
      apply (Ldext_nder (max (S n) x)). apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
      exists (nodup (@eq_dec_form _ _ eq_dec_preds eq_dec_funcs) ((list_disj (snd (Ldext (Init.Nat.max (S n) x)))) :: l)).
      repeat split ; auto. apply NoDup_nodup. intros A HA ; apply nodup_In in HA. inversion HA ; subst. left ; split.
      right ; apply Hl1 ; auto. apply list_disj_nodup. remember (Ldext (Init.Nat.max (S n) x)) as X. cbn.
      apply prv_DE with (list_disj L2) (list_disj l). apply (@prv_cut _ _ eq_dec_preds eq_dec_funcs _ _ _ Hl2).
      intros A HA ; inversion HA ; subst. inversion H0 ; subst. eapply MP. eapply list_conj_in_list with (l:=(fst (Ldext (Init.Nat.max (S (form_index (∃ phi))) x)))).
      apply Ldext_cum1 with x ; auto ; lia. apply Id ; split. inversion H0 ; subst.
      apply prv_list_conj. intros B HB. eapply MP. eapply list_conj_in_list with (l:=(fst (Ldext (Init.Nat.max (S (form_index (∃ phi))) x)))).
      apply Ldext_cum1 with (form_index (∃ phi)). lia. rewrite HL ; cbn ; auto. apply Id ; split. subst ; apply prv_DI1.
      apply list_disj_mono with L2. assert (L2 = snd (Ldext (form_index (∃ phi)))). rewrite HL ; auto. rewrite H0. apply Ldext_cum2 ; lia.
      apply Id ; right ; split. apply prv_DI2. apply Id ; right ; split.
      intros B HB ; inversion HB ; subst. apply prv_CI. apply Id ; left ; split. apply Id ; right ; split. }
    exists (proj1_sig (Ldext_ex n0)). exists (S n). cbn.
    rewrite HL.
    destruct form_all as [[]|]. rewrite Heqn in e. rewrite form_enum_index in e ; try discriminate.
    destruct form_ex as [[]|].
    - rewrite Heqn in e ; rewrite form_enum_index in e ; injection e. intros <-. rewrite HS. right. left. reflexivity.
    - contradict n2. exists phi. rewrite Heqn. apply form_enum_index.
  Qed.

  Lemma dext_all_henk :
    all_henk dext.
  Proof.
    intros phi HP. remember (form_index (∀ phi)) as n.
    destruct (Ldext n) as [L1 L2] eqn: HL.
    destruct (SLEM (pair_der (Singleton _ ((list_conj L1 --< ∀ phi) --< list_disj L2)) (Complement _ w))) eqn: HS.
    - exfalso. apply HP. exists (S n). cbn. rewrite HL. rewrite Heqn ; cbn. rewrite form_enum_index ; cbn.
      destruct form_all as [[]|].
      + injection e as ->. rewrite HS. now left.
      + contradict n0. now exists phi.
    - exists (proj1_sig (Ldext_all n0)). intro. destruct H as (c & Hc).
      apply (Ldext_nder (max (S n) c)). apply (@gen_FOBIH_Dual_Deduction_Theorem) ; auto.
      exists [(list_disj (snd (Ldext (Init.Nat.max (S n) c))))].
      repeat split ; auto. apply NoDup_cons. intro H ; inversion H. apply NoDup_nil.
      intros A HA ; inversion HA ; subst. left ; split. inversion H.
      remember (Ldext (Init.Nat.max (S n) c)) as X. cbn.
      eapply MP. apply Ax ; eapply A3 ; reflexivity. eapply MP. apply list_disj_In0. Unshelve. 3: exact phi[$(proj1_sig (Ldext_all n0))..]. subst.
      pose (Ldext_cum2 (S (form_index (∀ phi)))). apply i. lia. cbn. rewrite HL. rewrite form_enum_index.
      destruct form_all as [[]|]. inversion e ; subst. rewrite HS ; cbn. auto.
      exfalso ; apply n ; exists phi ;  auto. subst. eapply MP. apply list_conj_in_list.
      pose (Ldext_cum1 c (max (S (form_index (∀ phi))) c)). apply i ; auto. lia. apply Id ; split.
  Qed.

  Lemma dext_ded_clos :
    ded_clos dext.
  Proof.
    intros phi HP. destruct (form_enum_sur phi) as [n <-].
    exists (S n). cbn. destruct Ldext eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM eqn:EqD; cbn in * ; auto.
    - exfalso. rewrite e in HP. apply dext_nder with (S n).
      exists [(list_disj (snd (Ldext (S n))))]. repeat split. apply NoDup_cons. intro H ; inversion H. apply NoDup_nil.
      intros A HA ; inversion HA ; subst. left ; split. inversion H.
      remember (snd (Ldext (S n))) as X. cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. subst.
      apply prv_list_disj with (∀ x) ; auto. cbn. rewrite HL ; cbn. destruct form_all as [[]|].
      rewrite e in e0. inversion e0 ; subst. rewrite EqD ; cbn. auto. exfalso. apply n1. exists x ; firstorder.
    - exfalso. rewrite e in HP. apply dext_nder with (S n).
      exists [(list_disj (snd (Ldext (S n))))]. repeat split. apply NoDup_cons. intro H ; inversion H. apply NoDup_nil.
      intros A HA ; inversion HA ; subst. left ; split. inversion H.
      remember (snd (Ldext (S n))) as X. cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. subst.
      apply prv_list_disj with (∃ x) ; auto. cbn. rewrite HL ; cbn. destruct form_all as [[]|]. rewrite e0 in e. inversion e.
      destruct form_ex as [[]|]. rewrite e0 in e. inversion e ; subst. rewrite EqD ; cbn. auto.
      exfalso. apply n2. exists x ; firstorder.
    - exfalso. apply dext_nder with (S n).
      exists [(list_disj (snd (Ldext (S n))))]. repeat split. apply NoDup_cons. intro H ; inversion H. apply NoDup_nil.
      intros A HA ; inversion HA ; subst. left ; split. inversion H.
      remember (snd (Ldext (S n))) as X. cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. subst.
      apply prv_list_disj with (form_enum n) ; auto. cbn. rewrite HL ; cbn. destruct form_all as [[]|]. exfalso ; apply n0 ; exists x ; auto.
      destruct form_ex as [[]|]. exfalso ; apply n1 ; exists x ; auto. rewrite EqD ; cbn. auto.
  Qed.

  Lemma dext_A0 :
    dext A0.
  Proof.
    exists 0 ; cbn ; auto.
  Qed.

  Lemma dext_B0 :
    ~ dext B0.
  Proof.
    intros H. apply (dext_nder 0). exists [(list_disj (snd (Ldext 0)))].
    repeat split. apply NoDup_cons. intro H0 ; inversion H0. apply NoDup_nil.
    intros A HA ; inversion HA ; subst. left ; split. inversion H0.
    cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity. eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
  Qed.

  Lemma dext_consist :
    consist dext.
  Proof.
    intros H. apply dext_B0. apply dext_ded_clos.
    apply prv_MP with ⊥; trivial. apply EFQ.
  Qed.

  Lemma dext_prime :
    prime dext.
  Proof.
    intros phi psi HD.
    destruct (SLEM (dext phi)), (SLEM (dext psi)); try tauto.
    remember (form_index phi) as m.
    remember (form_index psi) as k.
    exfalso.
    assert (phi el (snd (Ldext (S m)))).
    { cbn. destruct Ldext eqn: HL. destruct (form_all (form_enum m)) eqn: EqAll. destruct s. subst.
      destruct (SLEM (pair_der (Singleton form ((list_conj l --< (∀ x)) --< list_disj l0)) (Complement form w))) eqn: EqD.
      exfalso. apply n. exists (S (form_index phi)). cbn. rewrite HL. rewrite EqAll. rewrite EqD. rewrite <- e.
      rewrite form_enum_index. cbn ; auto. cbn. rewrite <- e ; rewrite form_enum_index ; auto. 
      destruct (form_ex (form_enum m)) eqn: EqEx. destruct s. subst.
      destruct (SLEM (pair_der (Singleton form ((∃ x) ∧ list_conj l --< list_disj l0)) (Complement form w))) eqn: EqD.
      rewrite <- e ; rewrite form_enum_index ; cbn ; auto.
      exfalso. apply n. exists (S (form_index phi)). cbn. rewrite HL. rewrite EqAll. rewrite EqEx. rewrite EqD. rewrite <- e.
      rewrite form_enum_index. cbn ; auto.
      destruct (SLEM (pair_der (Singleton form (form_enum m ∧ list_conj l --< list_disj l0)) (Complement form w))) eqn: EqD.
      rewrite Heqm ; rewrite form_enum_index ; cbn ; auto.
      exfalso. apply n. exists (S (form_index phi)). cbn. rewrite <- Heqm. rewrite HL. rewrite EqAll. rewrite EqEx.
      rewrite EqD. rewrite Heqm. rewrite form_enum_index. cbn ; auto. }
    assert (psi el (snd (Ldext (S k)))).
    { cbn. destruct (Ldext k) eqn: HL. destruct (form_all (form_enum k)) eqn: EqAll. destruct s. subst.
      destruct (SLEM (pair_der (Singleton form ((list_conj l --< (∀ x)) --< list_disj l0)) (Complement form w))) eqn: EqD.
      exfalso. apply n0. exists (S (form_index psi)). cbn. rewrite HL. rewrite EqAll. rewrite EqD. rewrite <- e.
      rewrite form_enum_index. cbn ; auto. cbn. rewrite <- e ; rewrite form_enum_index ; auto. 
      destruct (form_ex (form_enum k)) eqn: EqEx. destruct s. subst.
      destruct (SLEM (pair_der (Singleton form ((∃ x) ∧ list_conj l --< list_disj l0)) (Complement form w))) eqn: EqD.
      rewrite <- e ; rewrite form_enum_index ; cbn ; auto.
      exfalso. apply n0. exists (S (form_index psi)). cbn. rewrite HL. rewrite EqAll. rewrite EqEx. rewrite EqD. rewrite <- e.
      rewrite form_enum_index. cbn ; auto.
      destruct (SLEM (pair_der (Singleton form (form_enum k ∧ list_conj l --< list_disj l0)) (Complement form w))) eqn: EqD.
      rewrite Heqk ; rewrite form_enum_index ; cbn ; auto.
      exfalso. apply n0. exists (S (form_index psi)). cbn. rewrite <- Heqk. rewrite HL. rewrite EqAll. rewrite EqEx.
      rewrite EqD. rewrite Heqk. rewrite form_enum_index. cbn ; auto. }
    apply dext_nder with (max (S m) (S k)).
    exists [(list_disj (snd (Ldext (Init.Nat.max (S m) (S k)))))]. repeat split. 
    - apply NoDup_cons. intro H1 ; inversion H1. apply NoDup_nil.
    - intros A HA ; inversion HA ; subst.
      + left ; split.
      + inversion H1.
    - eapply MP. apply Ax ; eapply A3 ; reflexivity.
      apply list_disj_mono with [phi;psi].
      + intros C HC. inversion HC ; subst.
         * eapply (Ldext_cum2 _ _ _ _ H).
         * inversion H1 ; subst.
           -- eapply (Ldext_cum2 _ _ _ _ H0).
           -- inversion H2.
      + cbn. eapply MP.
         * apply Or_imp_assoc. apply Ax ; eapply A3 ; reflexivity.
         * apply Id ; auto.
Unshelve. all: lia.
  Qed.

End DownLind_constr.




Open Scope type.

Lemma Down_Lindenbaum_lemma : forall w A B,
  consist w -> prime w -> ded_clos w ->
  ex_henk w -> all_henk w ->
  ~ (pair_der (Singleton _ A) (adj (Complement form w) B)) ->
      existsT2 w', consist w' *
                          prime w' *
                          ded_clos w' *
                          ex_henk w' *
                          all_henk w' *
                          (w' A) *
                          (~ (w' B)) *
                          (forall C, w' C -> w C).
Proof.
  intros w A B cons prim dedclos exh allh H.
  exists (dext w exh A B) ; auto. cbn ; repeat split ; auto.
  - apply dext_consist ; auto.
  - apply dext_prime ; auto.
  - apply dext_ded_clos ; auto.
  - apply dext_ex_henk ; auto.
  - apply dext_all_henk ; auto.
  - apply dext_A0.
  - apply dext_B0 ; auto.
  - apply dext_el ; auto.
Qed.

End DownLind.
