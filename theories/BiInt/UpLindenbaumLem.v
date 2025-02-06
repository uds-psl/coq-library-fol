Require Import FunctionalExtensionality.

Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.

From FOL Require Import ExistsT.
From FOL Require Import BiInt.BiInt SyntaxFeatures HilbertCalc LogicProp Properties 
StandardLinenbaumLem KripkeSemantics.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

Section UpLind.

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


Section UpLind_constr.

  Variable w : form -> Prop .
  Variable wall_henk : all_henk w.

  Lemma Lext_all {L1 L2 psi} :
    ~ FOBIH_prv w (L1 --> (∀ psi) ∨ L2)
    -> { c | ~ w (L1 --> psi[$c..] ∨ L2) }.
  Proof.
    intros HD. assert (~ w (∀ (L1)[↑] --> psi ∨ (L2)[↑])).
    - intros H. apply HD. apply prv_ctx in H. apply prv_DT. eapply prv_MP.
      + eapply (FOBIH_monot _ _ (Constant_Domain_Ax _ _)). intros phi [].
      + apply prv_AI. eapply FOBIH_subst in H. Unshelve. 2: exact ↑. cbn in H.
        apply prv_AE with $0 in H. cbn in H. rewrite !form_subst_help in H.
        apply <- prv_DT in H. apply (FOBIH_monot _ _ H). cbn.
        intros A [[B [-> HA]]| ->].
        * exists B. split; trivial. constructor. apply HA.
        * exists L1. split; trivial. constructor 2. reflexivity.
    - unfold all_henk in wall_henk. apply wall_henk in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Defined.

  Lemma Lext_ex {L1 L2 psi} :
    ~ FOBIH_prv w (L1 --> (∃ psi) --> L2)
    -> { c | ~ w (L1 --> psi[$c..] --> L2) }.
  Proof.
    intros HD. assert (~ w (∀ L1[↑] --> psi --> L2[↑])).
    - intros H. apply HD. apply prv_ctx in H. apply prv_DT.
      apply prv_EE. eapply FOBIH_subst in H. Unshelve. 2: exact ↑. cbn in H.
      apply prv_AE with $0 in H. cbn in H. rewrite !form_subst_help in H.
      apply <- prv_DT in H. apply (FOBIH_monot _ _ H). cbn.
      intros A [[B [-> HA]]| ->].
      + exists B. split; trivial. constructor. apply HA.
      + exists L1. split; trivial. constructor 2. reflexivity.
    - apply wall_henk in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Qed.

  Variable wconsist : consist w.
  Variable wded_clos : ded_clos w.
  Variable wex_henk : ex_henk w.
  Variable A0 B0 : form.

  Hypothesis w_nder : ~ (FOBIH_prv (fun x => w x \/ x = A0) B0).

  Fixpoint Lext (n : nat) : list form * list form :=
    match n with
    | 0 => ([A0], [B0])
    | S n => let (L1, L2) := Lext n in let phi := form_enum n in
            match form_all phi, form_ex phi with 
            | inl (exist _ psi _), _ => match SLEM (w |- (list_conj L1) --> (∀ psi) ∨ list_disj L2) with
                                     | inl _ => (∀ psi :: L1, L2)
                                     | inr H => (L1, ∀ psi :: psi[$(proj1_sig (Lext_all H))..] :: L2)
                                     end
            | _, inl (exist _ psi _) => match SLEM (w |- (list_conj L1) --> (∃ psi) --> list_disj L2) with
                                     | inl _ => (L1, ∃ psi :: L2)
                                     | inr H => (∃ psi :: psi[$(proj1_sig (Lext_ex H))..] :: L1, L2)
                                     end
            | _, _ => if SLEM (w |- list_conj (phi :: L1) --> list_disj L2)
                     then (L1, phi :: L2) else (phi :: L1, L2)
            end
    end.

  Lemma Lext_cum1 n n' :
    n <= n' -> incl (fst (Lext n)) (fst (Lext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Lext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Lext_cum2 n n' :
    n <= n' -> incl (snd (Lext n)) (snd (Lext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Lext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Lext_nder n :
    ~ (w |- list_conj (fst (Lext n)) --> list_disj (snd (Lext n))).
  Proof.
    induction n; intros HD.
    - cbn in HD. apply w_nder. eapply prv_DE.
      + eapply prv_MP; try apply (prv_weak _ _ _ HD); try firstorder. apply prv_CI.
        * apply prv_ctx. now right.
        * apply prv_Top.
      + apply prv_ctx. now right.
      + apply prv_exp. apply prv_ctx. now right.
    - cbn in *. destruct Lext, form_all as [[]|]; try destruct form_ex as [[]|];
        destruct SLEM; try destruct Lext_all; try destruct Lext_ex; subst; cbn in *.
      + apply IHn. apply prv_DT. apply prv_DT in f. eapply prv_DE; try apply f.
        * apply prv_DT, prv_DT. apply prv_cas_car. apply HD.
        * apply prv_ctx. now right.
      + apply Lext_all_der,wded_clos in HD. contradiction.
      + apply IHn. apply prv_DT. apply prv_DT in HD. eapply prv_DE; try apply HD.
        * apply prv_DT, prv_DT. apply f.
        * apply prv_ctx. now right.
      + pose (@Lext_ex_der _ _ eq_dec_preds eq_dec_funcs w l l0). cbn in f. apply f in HD ; clear f.
         apply wded_clos in HD. contradiction.
      + apply IHn. apply prv_DT. apply prv_DT in HD. eapply prv_DE; try apply HD.
        * apply prv_DT, prv_DT. apply prv_cas_car. apply f.
        * apply prv_ctx. now right.
      + apply n2. apply HD.
  Qed.

  Lemma Lext_A0 n :
    A0 el fst (Lext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Lext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

  Lemma Lext_B0 n :
    B0 el snd (Lext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Lext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

  Definition ext phi :=
    exists n, phi el fst (Lext n).

  Lemma ext_der n :
    ext |- list_conj (fst (Lext n)).
  Proof.
    apply prv_list_conj. intros A HA. apply prv_ctx. now exists n.
  Qed.

  Lemma ext_prv phi :
    ext |- phi -> exists n, (fun psi => w psi \/ psi el fst (Lext n)) |- phi.
  Proof.
    intros [L[H1 H2]] % (@prv_compact _ _ eq_dec_preds eq_dec_funcs). revert phi H2.
    induction L as [|psi L IH]; intros phi H2.
    - exists 0. cbn. eapply prv_weak; try apply H2. intros B [].
    - destruct (H1 psi) as [k Hk]; try now left. destruct IH with (psi --> phi) as [n Hn].
      + intros B HB. apply H1. now right.
      + apply prv_DT. eapply prv_weak; try apply H2. unfold Included, In. cbn. intuition.
      + exists (n + k). apply prv_DT in Hn. eapply prv_weak; try apply Hn.
          intros B [[]| ->]; try (now left); right; eapply Lext_cum1; try eassumption; lia.
  Qed.

  Lemma Lext_mono T n n' :
    n <= n' -> T |- list_disj (snd (Lext n)) -> T |- list_disj (snd (Lext n')).
  Proof.
    intros H. apply list_disj_mono. now apply Lext_cum2.
  Qed.
  
  Lemma ext_nder n :
    ~ (ext |- list_disj (snd (Lext n))).
  Proof.
    intros [k Hk] % ext_prv. apply (Lext_nder (k + n)).
    apply prv_DT. apply Lext_mono with n; try lia.
    eapply prv_cut; try apply Hk. intros B [H|H].
    - apply prv_ctx. now left.
    - apply prv_list_conj'. apply Lext_cum1 with k; trivial. lia.
      Unshelve. all: auto.
  Qed.

  Lemma ext_el phi :
    w phi -> ext phi.
  Proof.
    intros Hw. destruct (form_enum_sur phi) as [n <- Hn]. exists (S n). cbn.
    destruct Lext eqn: HL, form_all as [[psi H]|]; try destruct form_ex as [[psi H]|].
    all: destruct SLEM; cbn; try now left.
    + exfalso. apply n0. apply prv_DT, prv_DI1. apply prv_ctx. left. now rewrite <- H.
    + exfalso. apply Lext_nder with (n:=n). rewrite HL; cbn.
      rewrite <- !prv_DT in f. apply prv_DT. rewrite H in Hw.
      apply (prv_weak _ _ _ f). intros phi [[| ->]| ->]; unfold In; tauto.
    + exfalso. apply Lext_nder with (n:=n). rewrite HL; cbn.
      rewrite <- prv_cas_car, <- !prv_DT in f. apply prv_DT.
      apply (prv_weak _ _ _ f). intros phi [[| ->]| ->]; unfold In; tauto.
  Qed.

  Lemma ext_ex_henk :
    ex_henk ext.
  Proof.
    intros phi H.
    destruct (Lext (form_index (∃ phi))) as [L1 L2] eqn: HL.
    destruct (SLEM (FOBIH_prv w (list_conj L1 --> (∃ phi) --> list_disj L2))) eqn: HS.
    { exfalso. apply (ext_nder (form_index (∃ phi))). eapply prv_MP. 2: apply prv_ctx, H. eapply prv_MP. 
      - rewrite HL. apply (prv_weak _ _ _ f). intros psi HP. now apply ext_el.
      - change (ext |- list_conj (fst (L1, L2))). rewrite <- HL. apply ext_der. }
    exists (proj1_sig (Lext_ex n)). exists (S (form_index (∃ phi))). cbn.
    rewrite HL. pose (form_enum_index (∃ phi)).
    destruct form_all as [[]|]. rewrite e in e0. try discriminate.
    destruct form_ex as [[]|].
    - rewrite e in e0. injection e0. intros <-. rewrite HS. right. left. reflexivity.
    - contradict n1. now exists phi.
  Qed.

  Lemma ext_all_henk :
    all_henk ext.
  Proof.
    intros phi HP.
    destruct (Lext (form_index (∀ phi))) as [L1 L2] eqn: HL.
    destruct (SLEM (FOBIH_prv w (list_conj L1 --> (∀ phi) ∨ list_disj L2))) eqn: HS.
    - exfalso. apply HP. exists (S (form_index (∀ phi))). cbn.
      rewrite HL. destruct form_all as [[]|].
      + rewrite form_enum_index in e. injection e as ->. rewrite HS. cbn ; auto.
      + contradict n. now exists phi.
    - exists (proj1_sig (Lext_all n)). intro. apply (ext_nder (S (form_index (∀ phi)))).
      cbn. rewrite HL. destruct form_all as [[]|].
      + rewrite form_enum_index in e. injection e as ->. rewrite HS. cbn.
         apply prv_DI2, prv_DI1, prv_ctx ; auto.
      + contradict n0. now exists phi.
  Qed.

  Lemma Lext_all_in phi n :
    form_enum n = ∀ phi -> ~ (w |- list_conj (fst (Lext n)) --> (∀ phi) ∨ list_disj (snd (Lext n)))
    -> ∀ phi el snd (Lext (S n)).
  Proof.
    intros H1 H2. cbn. destruct Lext, form_all as [[]|].
    - destruct SLEM.
      + exfalso. rewrite H1 in e. injection e as ->. contradiction.
      + rewrite H1 in e. injection e as ->. now left.
    - contradict n0. exists phi. now rewrite H1.
  Qed.

  Lemma ext_ded_clos :
    ded_clos ext.
  Proof.
    intros phi HP. destruct (form_enum_sur phi) as [n <-].
    exists (S n). cbn. destruct Lext eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn in *.
    - rewrite e. now left.
    - exfalso. rewrite e in HP. apply (ext_nder (S n)). eapply prv_MP; try apply HP.
      apply list_disj_In0. apply Lext_all_in; try apply e. rewrite HL. apply n0.
    - exfalso. rewrite e in HP. apply (ext_nder n). rewrite HL.
      eapply prv_MP; try apply HP. eapply prv_MP; try apply (ext_der n).
      rewrite HL. eapply prv_weak; try apply f. intros phi H. now apply ext_el.
    - rewrite e. now left.
    - exfalso. apply (ext_nder n). rewrite HL. eapply prv_MP; try apply prv_CI.
      + eapply prv_weak; try apply f. intros phi H. now apply ext_el.
      + apply HP.
      + change (ext |- list_conj (fst (l, l0))). rewrite <- HL. apply (ext_der n).
    - now left.
  Qed.

  Lemma ext_A0 :
    ext A0.
  Proof.
    exists 0 ; cbn ; auto.
  Qed.

  Lemma ext_B0 :
    ~ ext B0.
  Proof.
    intros H. apply (ext_nder 0). apply prv_DI1, prv_ctx, H.
  Qed.

  Lemma ext_consist :
    consist ext.
  Proof.
    intros H. apply ext_B0. apply ext_ded_clos.
    apply prv_MP with ⊥; trivial. apply EFQ.
  Qed.

  Lemma ext_nel' phi :
    ~ ext phi -> exists n, (fun psi => w psi \/ psi = phi) |- list_disj (snd (Lext n)) \/ phi el fst (Lext n).
  Proof.
    intros HD. destruct (form_enum_sur phi) as [n <-].
    exists (S n). cbn. destruct Lext eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn in *.
    - right. left. now rewrite e.
    - left. rewrite e. apply prv_DI1. apply prv_ctx. now right.
    - left. rewrite e. apply prv_DI1. apply prv_ctx. now right.
    - right. left. now rewrite e.
    - left. apply prv_DI1. apply prv_ctx. now right.
    - right. now left.
  Qed.

  Lemma ext_nel phi :
    ~ ext phi -> exists n, (fun psi => w psi \/ psi = phi) |- list_disj (snd (Lext n)).
  Proof.
    intros HP. destruct (ext_nel' phi HP) as [n [H|H]].
    - exists n. apply H.
    - exfalso. apply HP. now exists n.
  Qed.

  Lemma ext_prime :
    prime ext.
  Proof.
    intros phi psi HD.
    destruct (SLEM (ext phi)), (SLEM (ext psi)); try tauto.
    apply ext_nel in n as [n H]. apply ext_nel in n0 as [n' H'].
    exfalso. apply (ext_nder (n + n')). eapply prv_DE.
    - apply prv_ctx. apply HD.
    - eapply Lext_mono; try eapply prv_weak; try apply H; try lia.
      intros theta [HT|HT]; [ left | right ]; try tauto. now apply ext_el.
    - eapply Lext_mono; try eapply prv_weak; try apply H'; try lia.
      intros theta [HT|HT]; [ left | right ]; try tauto. now apply ext_el.
  Qed.

End UpLind_constr.




Open Scope type.

Lemma Up_Lindenbaum_lemma : forall w A B,
  consist w -> prime w -> ded_clos w ->
  ex_henk w -> all_henk w ->
  ~ (FOBIH_prv (fun x => w x \/ x = A) B) ->
      existsT2 w', consist w' *
                          prime w' *
                          ded_clos w' *
                          ex_henk w' *
                          all_henk w' *
                          (w' A) *
                          (~ (w' B)) *
                          (forall C, w C -> w' C).
Proof.
  intros w A B cons prim dedclos exh allh H.
  exists (ext w allh A B). cbn ; repeat split ; auto.
  - apply ext_consist ; auto.
  - apply ext_prime ; auto.
  - apply ext_ded_clos ; auto.
  - apply ext_ex_henk ; auto.
  - apply ext_all_henk ; auto.
  - apply ext_A0.
  - apply ext_B0 ; auto.
  - intros C HC. apply ext_el ; auto.
Qed.

End UpLind.
