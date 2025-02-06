Require Import List.
Export ListNotations.
Require Import Lia.
Require Import Arith.
Require Import Coq.Vectors.Vector.
Require Import Ensembles.

From Undecidability.FOL Require Import Syntax.Facts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.

From FOL Require Import ExistsT.
From FOL Require Import BiInt.BiInt SyntaxFeatures HilbertCalc RemoveList LogicProp Properties.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import BiIntSyntax.

Section Lindenbaum.

Variable LEM : forall P, P \/ ~ P.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Existing Instance falsity_on.

Context {eq_dec_preds : eq_dec Σ_preds}.
Context {eq_dec_funcs : eq_dec Σ_funcs}.

Local Notation vec := t.

Section Properties.

(* Properties of theories. *)

Implicit Type X : form -> Prop.


Definition prime X := forall A B, X (A ∨ B) -> (X A \/ X B).
Definition consist X := ~ FOBIH_prv X ⊥.
Definition ded_clos X := forall A, FOBIH_prv X A -> X A.
Definition ex_henk X := forall A, X (∃ A) ->  {c | X A[$c..]}.
Definition all_henk X := forall A, ~ X (∀ A) -> {c| ~ X A[$c..] }.

Lemma list_disj_prime : forall Γ,
  ~ (FOBIH_prv Γ ⊥) ->
  prime Γ ->
  forall x, Γ (list_disj x) -> exists y, List.In y x /\ Γ y.
Proof.
intros Γ H. induction x ; cbn ; intros ; auto.
- exfalso ; auto. apply H. apply Id ; auto.
- apply H0 in H1. destruct H1 ; auto.
  + exists a ; split ; auto.
  + apply IHx in H1. destruct H1. destruct H1.
     exists x0 ; split ; auto.
Qed.

Lemma all_henk' : forall X, all_henk X -> forall A, (forall c, X A[$ c..]) -> X (∀ A).
Proof.
intros. destruct (LEM (X (∀ A))) ; auto.
apply X0 in H0. exfalso. destruct H0 as (c & Hc). apply Hc ; auto.
Qed.

End Properties.



Section unused.

Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma vec_in_map_if : forall n (v : vec term n) t sigma, vec_in t v -> vec_in t`[sigma] (Vector.map (subst_term sigma) v).
Proof.
induction v ; cbn ; intros ; auto.
- inversion X.
- inv X. apply vec_inB. apply vec_inS ; auto.
Qed.

Lemma vec_in_VectorIn_term : forall (n : nat) (v : vec term n) (t : term), vec_in t v -> Vector.In t v.
Proof.
induction n.
- intros. inversion X.
- intros. inversion X. subst. destruct H. apply In_cons_hd. destruct H. subst. apply In_cons_tl. apply IHn ; auto.
Qed.

Lemma vec_in_dec : forall (n : nat) (v : vec term n) (t : term), vec_in t v + (vec_in t v -> False).
Proof.
induction v ; cbn ; intros ; auto.
- right. intro. inversion X.
- destruct (IHv t). left. apply vec_inS ; auto.
  destruct (eq_dec_term eq_dec_funcs h t) ; subst. left. apply vec_inB.
  right. intros. inv X ; auto.
Qed.

Lemma VectorIn_vec_in_term : forall (n : nat) (v : vec term n) (t : term), Vector.In t v -> vec_in t v.
Proof.
induction v ; cbn ; intros ; auto.
- exfalso. inversion H.
- destruct (eq_dec_term eq_dec_funcs h t) ; subst. apply vec_inB.
  apply vec_inS. apply IHv. inv H ; auto. exfalso ; auto.
Qed.

Lemma vec_in_map : forall n (v : vec term n) (t : term) F, vec_in t (Vector.map F v) -> 
        (sigT (fun (t' : term) => prod (vec_in t' v) (t = F t'))).
Proof.
induction v.
- intros. cbn in X. inversion X.
- intros. cbn in *. inv X.
  + exists h ; split ; auto. apply vec_inB.
  + destruct (IHv t F X0) as (t' & H0 & H1). subst. exists t' ; split ; auto.
     apply vec_inS ; auto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.

Lemma vec_map_ext X Y (f g : X -> Y) n (v : vec X n) :
    (forall x, vec_in x v -> f x = g x) -> Vector.map f v = Vector.map g v.
Proof.
  intros Hext; induction v in Hext |-*; cbn.
  - reflexivity.
  - rewrite IHv, (Hext h). 1: reflexivity. apply vec_inB. intros. apply Hext. apply vec_inS. auto.
Qed.

 Inductive unused_term (n : nat) : term -> Prop :=
| ut_var m : (n <> m) -> unused_term n (var m)
| ut_func f v : (forall t, Vector.In t v -> unused_term n t) -> unused_term n (func f v).

Inductive unused (n : nat) : form -> Prop :=
| uf_bot : unused n ⊥
| uf_atom P v : (forall t, Vector.In t v -> unused_term n t) -> unused n (atom P v)
| uf_bin op phi psi : unused n phi -> unused n psi -> unused n (bin op phi psi)
| uf_quant q phi : unused (S n) phi -> unused n (quant q phi).

Definition unused_L n l := forall phi, List.In phi l -> unused n phi.
Definition unused_S n X := forall phi, Ensembles.In _ X phi -> unused n phi.
Definition First_unused n Γ:= (unused_S n Γ) /\ (forall m, (unused_S m Γ) -> n <= m).
Definition closed phi := forall n, unused n phi.
Definition closed_L l := forall phi, List.In phi l -> closed phi.
Definition closed_S X := forall phi, Ensembles.In _ X phi -> closed phi.

(* Interactions between unused and quantifiers. *)

Lemma subst_unused_term xi sigma P t :
    (forall x, (P x) \/ (~ (P x))) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused_term m t) ->
    subst_term xi t = subst_term sigma t.
Proof.
intros Hdec Hext Hunused. induction t using strong_term_indT; cbn;   cbn.
  - destruct (Hdec x) as [H % Hunused | H % Hext].
    + inversion H ; subst ; congruence.
    + congruence.
  - f_equal. apply vec_map_ext. intros t H'. apply (H t H'). intros n H2 % Hunused. inv H2. apply H1.
    apply vec_in_VectorIn_term ; auto.
Qed.

Lemma unused_subst_term : forall t m sigma,
        (forall n, unused_term m (sigma n)) ->
        unused_term m t ->
        unused_term m t`[sigma].
Proof.
apply (@strong_term_indT _ (fun t => forall (m : nat) (sigma : nat -> term),
(forall n : nat, unused_term m (sigma n)) -> unused_term m t -> unused_term m t`[sigma])).
- intros ; simpl. apply H.
- intros. simpl. inversion H1 ; subst ; resolve_existT ; auto.
  apply ut_func. intros. apply VectorIn_vec_in_term in H2. apply vec_in_map in H2.
  destruct H2 as (t' & H2 & H4). subst. apply H ; auto. apply H3. apply vec_in_VectorIn_term ; auto.
Qed.

Lemma unused_list_disj : forall n l, (forall A, List.In A l -> unused n A) -> unused n (list_disj l).
Proof.
induction l.
- intros. simpl. apply uf_bot.
- intros. simpl. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma unused_list_conj : forall n l, (forall A, List.In A l -> unused n A) -> unused n (list_conj l).
Proof.
induction l.
- intros. simpl. apply uf_bin ; apply uf_bot.
- intros. simpl. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma exist_unused_term_exists_First_unused : forall t n,
  (unused_term n t) ->
  (exists n, (unused_term n t) /\ (forall m, unused_term m t -> n <= m)).
Proof.
intro t.
pose (well_founded_induction lt_wf (fun z => unused_term z t -> exists n0 : nat, unused_term n0 t /\ (forall m : nat, unused_term m t -> n0 <= m))).
apply e. clear e. intros.
destruct (LEM (exists m : nat, unused_term m t /\ m < x)).
- destruct H1. destruct H1. apply (H _ H2) ; auto.
- exists x. split ; auto. intros. destruct (Nat.lt_ge_cases m x). exfalso. apply H1. exists m ; split ; auto. auto.
Qed.



Definition shift_P P n :=
    match n with
    | O => False
    | S n' => P n'
    end.

Lemma subst_unused_form xi sigma P phi :
    (forall x, (P x) \/ (~ P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> unused m phi) ->
    subst_form xi phi = subst_form sigma phi.
Proof.
  revert xi sigma P. induction phi using form_ind_falsity;
    intros xi sigma P Hdec Hext Hunused; cbn; cbn ; auto.
  - f_equal. apply vec_map_ext. intros s H. apply (subst_unused_term  Hdec Hext).
    intros m H' % Hunused. inv H'. apply H1 ; auto. apply vec_in_VectorIn_term ; auto.
  - rewrite IHphi1 with (sigma := sigma) (P := P). rewrite IHphi2 with (sigma := sigma) (P := P).
    all: try tauto. all: intros m H % Hunused; inversion H; repeat resolve_existT; auto.
  - erewrite IHphi with (P := shift_P P). 1: reflexivity.
    + intros [| x]; [now right| now apply Hdec].
    + intros [| m]; [reflexivity|]. intros Heq % Hext; unfold ">>"; cbn. unfold ">>". rewrite Heq ; auto.
    + intros [| m]; [destruct 1| ]. intros H % Hunused; inversion H; repeat resolve_existT; auto.
Qed.

Lemma subst_unused_single xi sigma n phi :
    unused n phi -> (forall m, n <> m -> xi m = sigma m) -> subst_form xi phi = subst_form sigma phi.
Proof.
intros Hext Hunused. apply subst_unused_form with (P := fun m => n = m).
all: intuition ; subst. assumption.
Qed.

Definition cycle_shift n x := if Nat.eq_dec n x then $0 else $(S x).

Lemma cycle_shift_subject n phi : unused (S n) phi -> phi[($n)..][cycle_shift n] = phi.
Proof.
intros H. rewrite subst_comp. rewrite (@subst_unused_single ($n.. >> subst_term (cycle_shift n)) var (S n) _ H).
apply subst_var.
intros m H'. unfold funcomp. unfold cycle_shift.
destruct (Nat.eq_dec n n); cbn ; try congruence. destruct m.
cbn. destruct (Nat.eq_dec n n); cbn ; try congruence.
cbn. destruct (Nat.eq_dec n m); cbn ; try congruence.
Qed.

Lemma cycle_shift_shift n phi : unused n phi -> phi[cycle_shift n] = phi[↑].
Proof.
intros H. apply (@subst_unused_single _ _ _ _ H). intros m ?. unfold cycle_shift. destruct (Nat.eq_dec n m).
subst. exfalso ; auto. auto.
Qed.

Theorem EC_unused : forall n Γ A B,
  unused_S n (fun x => Ensembles.In _ Γ x \/ x = B \/ x = ∃ A) ->
  FOBIH_prv Γ (A[$n..] → B) ->
  FOBIH_prv Γ ((∃ A) → B).
Proof.
intros. assert (unused (S n) A). unfold unused_S in H. pose (H (∃ A)).
assert (Ensembles.In form (fun x : form => Ensembles.In form Γ x \/ x = B \/ x = ∃ A) (∃ A)). unfold Ensembles.In ; auto.
apply H in H1. inv H1 ; subst ; auto.
pose (FOBIH_subst (cycle_shift n) H0). cbn in f.
pose (@cycle_shift_subject n A H1). rewrite e in f. clear e.
pose (@cycle_shift_shift n B). rewrite e in f.
2: apply H ; unfold In ; auto.
eapply EC. apply (FOBIH_monot f).
cbn ; intros C HC. inv HC ; subst.
destruct H2 ; subst. exists x ; split ; auto.
rewrite cycle_shift_shift ; auto. apply H. unfold Ensembles.In ; auto.
unfold Ensembles.In ; auto.
Qed.

Theorem Gen_unused : forall n Γ A,
  unused_S n (fun x => Ensembles.In _ Γ x \/ x = ∀ A) ->
  FOBIH_prv Γ A[$n..] ->
  FOBIH_prv Γ (∀ A).
Proof.
intros. assert (unused (S n) A). unfold unused_S in H. pose (H (∀ A)).
assert (Ensembles.In form (fun x : form => Ensembles.In form Γ x \/ x = ∀ A) (∀ A)).
unfold Ensembles.In ; auto.
apply H in H1. inv H1 ; auto.
pose (FOBIH_subst (cycle_shift n) H0). cbn in f.
pose (@cycle_shift_subject n A H1). rewrite e in f. clear e.
eapply Gen. apply (FOBIH_monot f).
cbn ; intros C HC. inversion HC ; subst.
destruct H2 ; subst. unfold Ensembles.In. exists x ; split ; auto.
rewrite cycle_shift_shift ; auto. apply H. unfold Ensembles.In ; auto.
Qed.

Lemma max_list_infinite_unused :
 forall l, (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n : nat, m <= n -> unused_term n t)) ->
(exists m : nat, (forall t, List.In t l -> (unused_term m t /\ (forall n : nat, m <= n -> unused_term n t)))).
Proof.
induction l ; intros.
- exists 0. intros. inversion H0.
- assert (J1: List.In a (a :: l)). apply in_eq.
  pose (H _ J1). destruct e. destruct H0.
  assert (J2: (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n : nat, m <= n -> unused_term n t))).
  intros. apply H. apply in_cons. auto. apply IHl in J2. destruct J2. exists (max x x0). intros. inversion H3.
  subst. split ; auto. apply H1 ; lia. intros. apply H1 ; auto. lia. split. apply H2 ; auto. lia. intros. apply H2 ; auto. lia.
Qed.

Lemma term_infinite_unused : forall (t : term), (exists n, (unused_term n t) /\ (forall m, n <= m -> unused_term m t)).
Proof.
intros. induction t.
- destruct x. exists 1. split. apply ut_var. intro. inversion H. intros. apply ut_var. lia. exists (S (S x)). split.
  apply ut_var. lia. intros. apply ut_var. lia.
- pose (VectorDef.to_list v).
  assert (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n, m <= n -> unused_term n t)).
  intros. apply IH.
  apply VectorSpec.to_list_In in H. auto. apply max_list_infinite_unused in H. destruct H. exists x. split.
  apply ut_func. intros.
  apply VectorSpec.to_list_In in H0. pose (H t). destruct a ; auto. intros. apply ut_func. intros.
  apply VectorSpec.to_list_In in H1. pose (H t). destruct a ; auto.
Qed.

Lemma term_exists_unused : forall (t : term), exists n, unused_term n t.
Proof.
intros. destruct (term_infinite_unused t) as (x & H0 & H1) ; exists x ; auto.
Qed.

Lemma form_unused : forall (A : form), (exists n, (unused n A) /\ forall m, n <= m -> unused m A).
Proof.
  intros. induction A using form_ind_falsity.
  - exists 0. split. apply uf_bot. intros. apply uf_bot.
  - pose (VectorDef.to_list t).
    assert (forall t : term, List.In t l -> exists m : nat, unused_term m t /\ (forall n, m <= n -> unused_term n t)).
    intros. apply term_infinite_unused. apply max_list_infinite_unused in H. destruct H. exists x. split.
    apply uf_atom. intros. apply VectorSpec.to_list_In in H0. pose (H t0). destruct a ; auto. intros. apply uf_atom. intros.
    apply VectorSpec.to_list_In in H1. pose (H t0). destruct a ; auto.
  - destruct IHA1. destruct H. destruct IHA2. destruct H1.
    exists (max x0 x). split. apply uf_bin. apply H0 ; lia. apply H2 ; lia. intros.
    apply uf_bin. apply H0 ; lia. apply H2 ; lia.
  - destruct IHA. destruct H. exists x. split. apply uf_quant. apply H0. lia. intros.
    apply uf_quant. apply H0. lia.
Qed.

Lemma form_exists_unused : forall (A : form), exists n, unused n A.
Proof.
intros. destruct (form_unused A) as (x & H0 & H1) ; exists x ; auto.
Qed.

Lemma list_form_infinite_unused : forall (l : list form), exists n, forall A, List.In A l -> 
      (unused n A) /\ forall m, n <= m -> unused m A.
Proof.
induction l ; intros.
- exists 0 ; intros ;  inversion H.
- destruct IHl. cbn. destruct (form_unused a) as (x0 & H0 & H1).
  exists (max x x0) ; intros. destruct H2 ; subst. split ; auto. apply H1 ; auto ; lia.
  intros. apply H1 ; auto ; lia. split ; auto. apply H ; auto ; lia.
  intros. apply H ; auto ; lia.
Qed.

End unused.







Print enum_form.


Variable form_enum : nat -> form.
Variable form_enum_unused : forall n, forall A m, form_enum m = A -> m <= n -> unused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.

Lemma form_index_inj A B :
  form_index A = form_index B -> A = B.
Proof.
  intros H. apply f_equal with (f := form_enum) in H. now rewrite !form_enum_index in H.
Qed.




Section Lindenbaum_construction.

Definition gen_choice_code (Γ Δ : @Ensemble (form)) (n :nat) : prod (Ensemble form) (Ensemble form) :=
match form_enum n with
  | quant q A => match q with
                             | All => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ (∀ A))) Δ) -> False) /\ x = (∀ A)))
                               (fun x => (In _ Δ x) \/ ((pair_der (Union _ Γ (Singleton _ (∀ A))) Δ) /\ (x = (∀ A) \/ (x = A[($n)..]))))
                             | Ex => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ (∃ A))) Δ) -> False) /\ (x = (∃ A) \/ (x = A[($n)..]))))
                                (fun x => Δ x \/ ((pair_der (Union _ Γ (Singleton _ (∃ A))) Δ) /\ x = (∃ A)))
            end
  | A => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ A)) Δ) -> False) /\ x = A))
                           (fun x => Δ x \/ ((pair_der (Union _ Γ (Singleton _ A)) Δ) /\ x = A))
end.

Fixpoint nextension_theory (Γ Δ : @Ensemble (form)) (n : nat) :  prod (Ensemble form) (Ensemble form) :=
match n with
| 0 => (Γ, Δ)
| S m => gen_choice_code (fst (nextension_theory Γ Δ m)) (snd (nextension_theory Γ Δ m)) m
end.

Definition extension_theory (Γ Δ : @Ensemble (form)) : prod (Ensemble form) (Ensemble form) :=
 pair (fun x => (exists n, In _ (fst (nextension_theory Γ Δ n)) x))
        (fun x => (exists n, In _ (snd (nextension_theory Γ Δ n)) x)).

End Lindenbaum_construction.



Section Properties_Lind.

Lemma nextension_theory_extens : forall n (Γ Δ: @Ensemble (form)) x,
    ( Γ x ->  (fst (nextension_theory Γ Δ n)) x) /\
    ( Δ x ->  (snd (nextension_theory Γ Δ n)) x).
Proof.
induction n.
- simpl. auto.
- simpl. intros. split ; intro.
  + pose (IHn Γ Δ x). destruct a. pose (H0 H). unfold gen_choice_code ; cbn.
     destruct (form_enum n) ; auto ; simpl ; unfold In ; auto. destruct q.
      ++ simpl. auto.
      ++ simpl. auto.
  + pose (IHn Γ Δ x). destruct a. pose (H1 H). unfold gen_choice_code.
     destruct (form_enum n) ; auto ; simpl ; unfold In ; auto. destruct q.
      ++ simpl. auto.
      ++ simpl. auto.
Qed.

(* Each step creates an extension of the theory in the previous step. *)

Lemma nextension_theory_extens_le : forall m n (Γ Δ: @Ensemble (form)) x,
    ((fst (nextension_theory Γ Δ n)) x -> (le n m) -> (fst (nextension_theory Γ Δ m)) x) /\
    ((snd (nextension_theory Γ Δ n)) x -> (le n m) -> (snd (nextension_theory Γ Δ m)) x).
Proof.
induction m.
- intros. split ; intros ; simpl ; inversion H0 ; subst ; simpl in H ; auto.
- intros. split ; intros ; inversion H0.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (form_enum m); simpl ; auto. destruct q ; simpl ; auto.
  + subst. auto.
  + subst. simpl. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (form_enum m) ; simpl ; auto. destruct q ; simpl ; auto.
Qed.

Lemma extension_theory_extens_nextension : forall n (Γ Δ: @Ensemble (form)) x,
    ( (fst (nextension_theory Γ Δ n)) x ->  (fst (extension_theory Γ Δ)) x) /\
    ( (snd (nextension_theory Γ Δ n)) x ->  (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists n ; auto.
Qed.

(* So the resulting theory is an extension of the initial theory. *)

Lemma extension_theory_extens : forall (Γ Δ: @Ensemble (form)) x,
    (Γ x ->  (fst (extension_theory Γ Δ)) x) /\
    (Δ x ->  (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists 0 ; auto.
Qed.

(* The extension preserves derivability. *)

Lemma der_nextension_theory_mextension_theory_le : forall n m Γ Δ A,
  (FOBIH_prv (fst (nextension_theory Γ Δ n)) A) -> (le n m) ->
    (FOBIH_prv  (fst (nextension_theory Γ Δ m)) A).
Proof.
intros.
pose (FOBIH_monot (fst (nextension_theory Γ Δ n)) A H (fst (nextension_theory Γ Δ m))).
cbn in f. apply f. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma pair_der_nextension_theory_mextension_theory_le : forall n m Γ Δ A,
  (pair_der (fst (nextension_theory Γ Δ n)) (Singleton _ A)) -> (le n m) ->
    (pair_der  (fst (nextension_theory Γ Δ m)) (Singleton _ A)).
Proof.
intros. destruct H. destruct H. destruct H1. cbn in H1. cbn in H2.
destruct x.
- cbn in H2. pose (FOBIH_monot (fst (nextension_theory Γ Δ n)) ⊥ H2 (fst (nextension_theory Γ Δ m))).
  cbn in f. exists []. repeat split ; auto. cbn. apply f. intro. intros.
  apply nextension_theory_extens_le with (n:=n) ; auto.
- cbn in H2. cbn in H1. destruct x. cbn in H2. apply absorp_Or1 in H2.
  assert (List.In f (f :: List.nil)). apply in_eq. apply H1 in H3. inversion H3. subst.
  exists [f]. repeat split ; auto. cbn.
  eapply MP. apply Ax ; eapply A3 ; reflexivity.
  pose (FOBIH_monot (fst (nextension_theory Γ Δ n)) f H2 (fst (nextension_theory Γ Δ m))).
  apply f0. cbn. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
  exfalso. inversion H. apply H5. subst. assert (J1: List.In f (f :: f0 :: x)). apply in_eq.
  apply H1 in J1. inversion J1 ; subst. assert (J2: List.In f0 (f :: f0 :: x)). apply in_cons.
  apply in_eq. apply H1 in J2. inversion J2 ; subst. apply in_eq.
Qed.

(* The extension preserves relative consistency. *)

Lemma Under_pair_add_left_or_right : forall Γ Δ A, ~ pair_der Γ Δ ->
  ((pair_der (Union _ Γ (Singleton _ A)) Δ)  -> False) \/  (pair_der Γ (Union _ Δ (Singleton _ A))  -> False).
Proof.
intros.
destruct (LEM (pair_der (Union _ Γ (Singleton _ A)) Δ)) ; auto.
destruct (LEM (pair_der Γ (Union _ Δ (Singleton _ A)))) ; auto.
exfalso. apply H. apply (Cut _ _ _ H0 H1).
Qed.

Lemma unused_term_after_subst t sigma y :
  (forall x, unused_term x t \/ unused_term y (sigma x)) -> unused_term y (subst_term sigma t).
Proof.
  revert sigma y.
  apply (strong_term_ind (fun t => forall (sigma : nat -> term) (y0 : nat),
  (forall x : nat, unused_term x t \/ unused_term y0 (sigma x)) -> unused_term y0 t`[sigma])) ; cbn.
  - intros x sigma y H ; destruct (H x) ; auto. exfalso ; inversion H0 ; auto.
  - intros F v IH sigma y H. constructor. intros.
    apply VectorIn_vec_in_term in H0. apply vec_in_map in H0.
    destruct H0 as (t1 & H1 & H2) ; subst. apply (IH _ H1 sigma y).
    intros. destruct (H x) ; auto. left. inv H0. apply H3. apply vec_in_VectorIn_term ; auto.
Qed.

Lemma unused_after_subst phi sigma y :
  (forall x, unused x phi \/ unused_term y (sigma x)) -> unused y (subst_form sigma phi).
Proof.
  revert sigma y.
  induction phi.
  1-2: intros sigma y H ; constructor.
  - intros sigma y H. constructor. intros t0 H0. apply VectorIn_vec_in_term, vec_in_map in H0.
    destruct H0 as (t1 & H1 & H2) ; subst. apply unused_term_after_subst.
    intros. destruct (H x) ; auto. left. inv H0.  apply H3. apply vec_in_VectorIn_term ; auto.
  - intros sigma y H. constructor.
    + apply IHphi1. intro x. destruct (H x) ; auto. left. inv H0 ; auto.
    + apply IHphi2. intro x. destruct (H x) ; auto. left. inv H0 ; auto.
  - intros sigma y H. cbn. constructor.
    apply IHphi. intros [].
    + right. cbn. constructor. lia.
    + destruct (H n) as [Hn|Hn].
      * inversion Hn; subst. now left.
      * right. cbn. unfold funcomp. apply unused_term_after_subst.
        intros x. assert (x = y \/ x <> y) as [->|Hy] by lia; auto.
        right. constructor. lia.
Qed.

Lemma nextension_infinite_unused : forall n m (Γ Δ: @Ensemble (form)),
  (closed_S Γ) ->
  (closed_S Δ) ->
  (n <= m) ->
  unused_S m (fun y : form => (fst (nextension_theory Γ Δ n)) y \/ (snd (nextension_theory Γ Δ n)) y).
Proof.
induction n ; cbn ; intros m Γ Δ HΓ HΔ H A HA.
- inversion HA ; auto.
  + apply HΓ ; auto.
  + apply HΔ ; auto.
- destruct HA.
  + unfold gen_choice_code in H0. destruct (form_enum n) eqn:E; cbn in H0.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. left ; auto.
        -- apply uf_⊥.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. left ; auto.
        -- apply uf_top.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. left ; auto.
        -- apply form_enum_unused with n ; auto. lia.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. left ; auto.
        -- apply form_enum_unused with n ; auto. lia.
     * destruct q ; cbn in *.
        -- destruct H0 as [H0 | (H0 & H1)] ; subst.
          ++ apply (IHn m Γ Δ) ; auto. lia. left ; auto.
          ++ apply form_enum_unused with n ; auto. lia.
        -- destruct H0 as [H0 | (H0 & H1)] ; subst.
          ++ apply (IHn m Γ Δ) ; auto. lia. left ; auto.
          ++ destruct H1 ; subst.
               ** apply form_enum_unused with n ; auto. lia.
               ** apply unused_after_subst. intro x. destruct x ; cbn.
                   --- right. apply ut_var ; lia.
                   --- destruct (Nat.eq_dec x m) ; subst.
                       +++ left. assert (unused m (∃ f)).
                              { apply form_enum_unused with n ; auto. lia. }
                              inversion H1 ; auto.
                       +++ right. apply ut_var ; auto.
  + unfold gen_choice_code in H0. destruct (form_enum n) eqn:E; cbn in H0.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. right ; auto.
        -- apply uf_⊥.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. right ; auto.
        -- apply uf_top.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. right ; auto.
        -- apply form_enum_unused with n ; auto. lia.
     * destruct H0 as [H0 | (H0 & H1)] ; subst.
        -- apply (IHn m Γ Δ) ; auto. lia. right ; auto.
        -- apply form_enum_unused with n ; auto. lia.
     * destruct q ; cbn in *.
        -- destruct H0 as [H0 | (H0 & H1)] ; subst.
          ++ apply (IHn m Γ Δ) ; auto. lia. right ; auto.
          ++ destruct H1 ; subst.
               ** apply form_enum_unused with n ; auto. lia.
               ** apply unused_after_subst. intro x. destruct x ; cbn.
                   --- right. apply ut_var ; lia.
                   --- destruct (Nat.eq_dec x m) ; subst.
                       +++ left. assert (unused m (∀ f)).
                              { apply form_enum_unused with n ; auto. lia. }
                              inversion H1 ; auto.
                       +++ right. apply ut_var ; auto.
        -- destruct H0 as [H0 | (H0 & H1)] ; subst.
          ++ apply (IHn m Γ Δ) ; auto. lia. right ; auto.
          ++ apply form_enum_unused with n ; auto. lia.
Qed.

Lemma Under_nextension_theory : forall n Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  (pair_der Γ Δ -> False) ->
  (pair_der (fst (nextension_theory Γ Δ n)) (snd (nextension_theory Γ Δ n)) -> False).
Proof.
induction n ; intros Γ Δ ClΓ ClΔ ; intros.
- cbn in H0. auto.
- cbn in H0. apply IHn with (Γ:=Γ) (Δ:=Δ) ; auto. unfold gen_choice_code in H0.
  destruct (form_enum n) eqn:E; auto ; destruct H0 ; destruct H0 ; destruct H1.
    (* Then in each case check if either adding to the left or the right preserve provability. *)

    (* Bot *)
    * cbn in *. assert (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥)) (snd (nextension_theory Γ Δ n))).
      exists []. repeat split ; auto. apply NoDup_nil. intros. inversion H3. cbn. apply Id. right. apply In_singleton.
      assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
     (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥)) (snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊥) =
     (fst (nextension_theory Γ Δ n))).
     apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5. exfalso ; auto. unfold In.
     left ; auto. rewrite H4 in H2. clear H4. exists (remove eq_dec_form ⊥ x). repeat split ; auto. apply NoDup_remove ; auto.
     intros. assert (List.In A x). apply in_remove in H4. destruct H4. auto.
     apply H1 in H5. inversion H5 ; auto. destruct H6 ; destruct H7 ; subst. exfalso. apply remove_not_in_anymore in H4. auto.
     apply der_list_disj_⊥. auto.
    (* Atom *)
    * cbn in *. destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (LEM (pair_der (fst (nextension_theory Γ Δ n)) (Union form (snd (nextension_theory Γ Δ n)) (Singleton form (atom P t))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (atom P t)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. cbn.
             inversion H5 ; auto. left ; auto. destruct H6 ; destruct H7 ; subst. right.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion o ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (atom P t))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
        destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    (* Binary operator *)
    * cbn in H1. cbn in H2.
      destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (LEM (pair_der (fst (nextension_theory Γ Δ n)) (Union form (snd (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (bin b f1 f2)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. cbn.
             inversion H5 ; auto. left ; auto. destruct H6 ; destruct H7 ; subst. right.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion o ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (bin b f1 f2))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
        destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    (* Quantifiers *)
    * destruct q.
      -- cbn in *.
         destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)))).
         ++ assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
            (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)) -> False) /\
            x = ∀ f) = (fst (nextension_theory Γ Δ n))).
            { apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto. }
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. cbn in H4. destruct H4.
            apply FOBIH_Deduction_Theorem in H5.
            exists (nodup eq_dec_form (remove eq_dec_form f[$n..] (x ++ x0))).
            repeat split ; auto. apply NoDup_nodup.
            intros A H8. apply nodup_In in H8.
            apply in_remove in H8. destruct H8 as (H8 & H9). apply in_app_or in H8 ; destruct H8.
            apply H1 in H6. unfold In in * ; cbn in *. destruct H6 ; subst. left ; auto.
            destruct H6 as (H11 & H12). destruct H12 ; subst. right ; apply In_singleton. exfalso ; auto. left. apply H4 ; auto.
            apply list_disj_nodup.
            pose (remove_disj (x ++ x0) f[$n..] (fst (nextension_theory Γ Δ n))). cbn in *.
            assert (FOBIH_prv (fst (nextension_theory Γ Δ n)) (f[$n..] ∨ list_disj (remove eq_dec_form f[$n..] (x ++ x0)))).
            eapply MP. exact f0. eapply MP. apply Id_list_disj ; auto. exact H2.
            assert (unused_S n (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/ x1 = ∀ (f ∨ (list_disj (remove eq_dec_form f[$n..] (x ++ x0)))[↑]))).
            {
            intros A HA. unfold In in * ; cbn in *.
            destruct HA ; subst. pose (nextension_infinite_unused n n _ _ ClΓ ClΔ). apply u ; auto.
            unfold In. left ; auto. apply uf_quant. apply uf_bin. apply form_enum_unused with (n:=n) in E.
            inversion E ; subst ;auto. lia.
            apply unused_after_subst ; auto. intro n0. 
            assert (n0 = n \/ n <> n0) as [Hn|Hn] by lia.
            { 
              subst. left. apply unused_list_disj. intros. apply in_remove in H7. destruct H7.
              apply in_app_or in H7 ; destruct H7. apply H1 in H7. destruct H7.
              pose (nextension_infinite_unused n n _ _ ClΓ ClΔ). apply u ; auto. right ; auto. destruct H7.
              destruct H9 ; subst. apply form_enum_unused with n ; auto. exfalso ; auto.
              apply H4 in H7.  pose (nextension_infinite_unused n n _ _ ClΓ ClΔ). apply u ; auto. right ; auto.
            }
            right. apply ut_var. congruence.
            }
            pose (Gen_unused _ _ _ H7). cbn in f1. rewrite subst_shift in f1. apply f1 in H6.
            clear f1.
            assert (FOBIH_prv (fst (nextension_theory Γ Δ n)) ((∀ f) ∨ (list_disj (remove eq_dec_form f[$n..] (x ++ x0))))).
            eapply MP. apply FOBIH_monot with (Γ:=Empty_set _). apply Constant_Domain_Ax. intros C HC ; inversion HC. auto.
            eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
            2: apply imp_Id_gen. 2: exact H8. eapply MP. eapply MP. apply Imp_trans.
            exact H5. rewrite remove_app. apply list_disj_app0. eapply MP. eapply MP. apply Imp_trans.
            2: apply Ax ; eapply A4 ; reflexivity. rewrite notin_remove. apply imp_Id_gen.

            intro H9. apply (IHn Γ Δ) ; auto.
            exists (nodup eq_dec_form (remove eq_dec_form (∀ f) (x ++ x0))).
            repeat split ; auto. apply NoDup_nodup.
            intros A H10. apply nodup_In in H10.
            apply in_remove in H10. destruct H10 as (H10 & H11). apply in_app_or in H10 ; destruct H10.
            apply H1 in H10. unfold In in * ; cbn in *. destruct H10 ; subst ; auto.
            destruct H10 as (H12 & H13). destruct H13 ; subst. exfalso ; auto. 1-2: apply H4 ; auto. 
            apply list_disj_nodup.
            pose (remove_disj (x ++ x0) (∀ f) (fst (nextension_theory Γ Δ n))). cbn in *.
            assert (FOBIH_prv (fst (nextension_theory Γ Δ n)) ((∀ f) ∨ list_disj (remove eq_dec_form (∀ f) (x ++ x0)))).
            eapply MP. exact f1. eapply MP. apply Id_list_disj ; auto. exact H2.
            eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
            2: apply imp_Id_gen. 2: exact H10. apply FOBIH_Deduction_Theorem.
            apply list_disj_In with f[$n..]. apply in_not_touched_remove. apply in_or_app ; auto.
            intro. assert (size f[$n..] = size (∀ f)). rewrite <- H11 ; auto. rewrite subst_size in H12.
            destruct f ; cbn in H12 ; lia. eapply MP. eapply MP. eapply MP. apply Imp_trans.
            2: apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply QA2 ; reflexivity. apply Id. right ; apply In_singleton.
         ++ assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ x = ∀ f) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∀ f))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
            destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
            subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
            apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto.
      -- cbn in H2.
          destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)))).
          { assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ (x = ∃ f \/ x = f[$n..])) = (fst (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. cbn in H4. destruct H4.
            exists (x0 ++ remove_list x0 x). repeat split. apply add_remove_list_preserve_NoDup ; auto. intros.
            cbn. apply in_app_or in H6. destruct H6. left ; apply H4 ; auto. apply In_remove_list_In_list in H6.
            apply H1 in H6. inversion H6. left ; auto. destruct H7. subst. right ; apply In_singleton.
            cbn. eapply MP. apply Id_list_disj_remove. auto. }
          { assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ (x = ∃ f \/ x = f[$n..])) = Union _ (Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∃ f))) (Singleton _ f[$n..])).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; left ; auto.
            destruct H5. destruct H6. subst. left ; right. apply In_singleton. unfold In. subst. right ; apply In_singleton.
            unfold In in *. destruct H4. destruct H4. auto. right. split ; auto. left ; inversion H4 ; subst ; auto. inversion H4 ; subst.
            right. split ; auto. rewrite H4 in H2. clear H4.
            assert ((fun x : form => snd (nextension_theory Γ Δ n) x \/
            pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) /\
            x = ∃ f) = (snd (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4. auto. destruct H5. exfalso ; auto. unfold In ; auto.
            rewrite H4 in H1. clear H4.
            apply FOBIH_Deduction_Theorem with (A:=f[$n..]) (B:=list_disj x)
            (Γ:=(Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)))) in H2 ; auto.
            assert (J1: FOBIH_prv (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (list_disj x)).
            eapply MP. apply EC_unused with (n:=n) ; auto.
            intros A HA. unfold In in * ; cbn in *.
            destruct HA ; subst. inversion H4 ; subst.
            pose (nextension_infinite_unused n n _ _ ClΓ ClΔ). apply u ; auto.
            unfold In. left ; auto. inversion H5 ; subst. apply form_enum_unused with n ; auto. destruct H4 ; subst.
            2: apply form_enum_unused with n ; auto ; exact E. apply unused_list_disj. intros. apply H1 in H4.
            pose (nextension_infinite_unused n n _ _ ClΓ ClΔ). apply u ; auto. right ; auto. auto. 
            apply Id ; right ; apply In_singleton. exfalso. apply H3. exists x. repeat split ; auto.
            }
Qed.

Lemma form_index_In_L_or_R : forall (A : form) Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  (fst (nextension_theory Γ Δ (S (form_index A)))) A \/  (snd (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. cbn. unfold gen_choice_code.
rewrite form_enum_index.
destruct A ; cbn.
- right. right. split ; auto. exists []. repeat split ; auto.
  apply NoDup_nil. intros. inversion H2. cbn. apply Id. right.
  apply In_singleton.
- simpl. left. unfold In. right. repeat split ; auto. intros.
  apply (Under_nextension_theory (form_index ⊤) _ _ H H0 H1).
  assert (pair_der ((fst (nextension_theory Γ Δ (form_index ⊤)))) (Union form (snd (nextension_theory Γ Δ (form_index ⊤))) (Singleton form ⊤))).
  exists [⊤]. repeat split ; auto. apply NoDup_cons. intro. inversion H3. apply NoDup_nil.
  intros. inversion H3. apply Union_intror. subst. apply In_singleton. inversion H4.
  simpl. eapply MP. apply Ax ; eapply A3 ; reflexivity. apply prv_Top.
  pose (Cut _ _ _ H2 H3). auto.
- cbn. destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (atom P t)))) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ (form_index (atom P t)))))).
  right. unfold In. right. repeat split ; auto. unfold In. left. right. split ; auto.
- cbn. destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (bin b A1 A2)))) (Singleton form (bin b A1 A2))) (snd (nextension_theory Γ Δ (form_index (bin b A1 A2)))))).
  right. unfold In. right. repeat split ; auto. left. unfold In. right. auto.
- cbn. destruct q.
  + cbn. destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∀ A)))) (Singleton form (∀ A))) (snd (nextension_theory Γ Δ (form_index (∀ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right ; auto.
  + cbn. destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∃ A)))) (Singleton form (∃ A))) (snd (nextension_theory Γ Δ (form_index (∃ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right. repeat split ; auto.
Qed.

Lemma In_extension_In_form_index_L : forall A Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
   (fst (extension_theory Γ Δ)) A ->
   (fst (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. pose (form_index_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. cbn in H2. inversion H2.
pose (Nat.max_dec x (S (form_index A))). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (S (form_index A0))) (S (form_index A0)) Γ Δ A0).
destruct a ; auto. apply H7 in H3 ; try lia. rewrite e in H3 ; auto. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
apply (Under_nextension_theory (S (form_index A)) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (S (form_index A0))) x Γ Δ A0).
destruct a. apply H6 in H4 ; try lia. rewrite e in H4 ; auto. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le (S (form_index A)) x Γ Δ A).
unfold In in *. destruct a. cbn in H5. apply H5. 2: lia. auto.
Qed.

Lemma In_extension_In_form_index_R : forall A Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
   (snd (extension_theory Γ Δ)) A ->
   (snd (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. pose (form_index_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. cbn in H2. inversion H2.
pose (Nat.max_dec x (S (form_index A))). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6. auto.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le x (S (form_index A)) Γ Δ A).
destruct a. apply H5 ; try lia ; auto.
apply (Under_nextension_theory (S (form_index A)) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (S (form_index A0)) x Γ Δ A0).
destruct a. apply H7 ; try lia ; auto.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le (form_index A) x Γ Δ A).
destruct a. auto.
Qed.

Lemma max_list_form_index : forall l, (exists m, forall n, (exists A, form_index A = n /\ List.In A l) -> n <= m).
Proof.
induction l.
- exists 0. intros. destruct H. destruct H. inversion H0.
- destruct IHl. exists (Nat.max (form_index a) x). intros. destruct H0. destruct H0.
  inversion H1. subst. lia. subst.
  assert (exists A : form, form_index A = form_index x0 /\ List.In A l). exists x0 ; auto.
  pose (H (form_index x0) H0). lia.
Qed.

Lemma Under_extension_theory : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (extension_theory Γ Δ)) (snd (extension_theory Γ Δ)).
Proof.
intros Γ Δ ClΓ ClΔ H H0. unfold extension_theory in H0. destruct H0. destruct H0. destruct H1. cbn in H1.
cbn in H2. pose (FOBIH_finite _ _ H2). destruct e. cbn in H3. destruct H3. destruct H4. destruct H5.
assert (exists ml, forall n, (exists A, form_index A = n /\ List.In A x1) -> n <= ml).
apply max_list_form_index. destruct H6.
assert (exists mr, forall n, (exists A, form_index A = n /\ List.In A x) -> n <= mr).
apply max_list_form_index. destruct H7.
pose (Under_nextension_theory (S (max x2 x3)) _ _ ClΓ ClΔ H). apply f.
exists x. repeat split ; auto.
intros. pose (H1 _ H8). pose (In_extension_In_form_index_R A _ _ ClΓ ClΔ H).
assert ( (snd (extension_theory Γ Δ)) A). destruct e. exists x4 ; auto. apply s in H9.
pose (nextension_theory_extens_le (S (Init.Nat.max x2 x3)) (S (form_index A)) Γ Δ A).
destruct a. apply H11 ; auto. assert (exists A0 : form, form_index A0 = form_index A /\ List.In A0 x).
exists A ; auto. pose (H7 (form_index A) H12). lia.
apply (FOBIH_monot _ _ H4). cbn. intro. intro.
pose (In_extension_In_form_index_L x4 _ _ ClΓ ClΔ H).
pose (H3 _ H8). pose (H5 x4). destruct p. pose (i0 H8).
pose (nextension_theory_extens_le (S (Init.Nat.max x2 x3)) (S (form_index x4)) Γ Δ x4).
destruct a. apply H9 ; auto. assert (exists A : form, form_index A = form_index x4 /\ List.In A x1).
exists x4 ; auto. pose (H6 (form_index x4) H11). lia.
Qed.




(* The extension is consistent. *)

Lemma Consist_nextension_theory : forall n Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (nextension_theory Γ Δ n)) (Singleton _ ⊥).
Proof.
intros n Γ Δ ClΓ ClΔ H H0. pose (Under_nextension_theory n Γ Δ ClΓ ClΔ H).
apply f. exists []. repeat split ; auto. apply NoDup_nil.
intros. inversion H1. cbn. destruct H0. destruct H0. destruct H1.
cbn in H2. cbn in H1. destruct x. cbn in H2 ; auto.
destruct x. assert (J1: List.In f0 (f0 :: List.nil)). apply in_eq. pose (H1 _ J1).
inversion s ; subst ; auto. cbn in H2. apply absorp_Or2. auto.
exfalso.  assert (J1: List.In f0 (f0 :: f1 :: x)). apply in_eq.
apply H1 in J1. inversion J1. subst. assert (J2: List.In f1 (⊥ :: f1 :: x)).
apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. subst. apply H5. apply in_eq.
Qed.

Lemma Consist_extension_theory_pair : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (extension_theory Γ Δ)) (Singleton _ ⊥).
Proof.
intros Γ Δ ClΓ ClΔ H H0. destruct H0. destruct H0. destruct H1.
cbn in H2. cbn in H1. apply (Under_extension_theory Γ Δ) ; auto. exists [].
repeat split ; auto. apply NoDup_nil. intros. inversion H3.
cbn. destruct x. cbn in H2. auto. destruct x.
assert (J1: List.In f (f :: List.nil)). apply in_eq. apply H1 in J1. inversion J1. subst. cbn in H2.
apply absorp_Or1 ; auto. exfalso.
assert (J1: List.In f (f :: f0 :: x)). apply in_eq. apply H1 in J1. inversion J1. subst.
assert (J2: List.In f0 (⊥ :: f0 :: x)). apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. apply H5 ; subst ; apply in_eq.
Qed.

Lemma Consist_extension_theory : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  consist (fst (extension_theory Γ Δ)).
Proof.
intros Γ Δ ClΓ ClΔ D0 D1.
apply (Consist_extension_theory_pair _ _ ClΓ ClΔ D0).
exists []. repeat split ; auto. apply NoDup_nil. intros. inversion H.
Qed.


(* The extension is deductively closed. *)

Lemma closeder_fst_Lind_pair : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  ded_clos (fst (extension_theory Γ Δ)).
Proof.
intros. intros A HA. destruct (form_index_In_L_or_R A _ _ H H0 H1).
- apply extension_theory_extens_nextension in H2 ; auto.
- exfalso. apply Under_extension_theory with Γ Δ ; auto.
  exists [A] ; cbn. repeat split ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
  intros B HB. inversion HB ; [ subst ; apply extension_theory_extens_nextension in H2 ; auto | inversion H3].
  eapply MP. apply Ax ; eapply A3 ; reflexivity. auto.
Qed.


(* The extension is prime. *)

Lemma primeness_fst_Lind_pair : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  prime (fst (extension_theory Γ Δ)).
Proof.
intros. intros A B Hor.
destruct (form_index_In_L_or_R A _ _ H H0 H1).
- left. apply extension_theory_extens_nextension in H2 ; auto.
- destruct (form_index_In_L_or_R B _ _ H H0 H1).
  + right. apply extension_theory_extens_nextension in H3 ; auto.
  + apply extension_theory_extens_nextension in H2,H3. exfalso.
     apply Under_extension_theory with Γ Δ ; auto.
     destruct (eq_dec_form A B) ; subst.
     * exists [B] ; cbn. repeat split ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros C HC. inversion HC ; [ subst ; auto | inversion H4].
       eapply MP. 2: apply Id ; exact Hor. eapply MP. eapply MP.
       2,3: apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A5 ; reflexivity.
     * exists [A;B] ; cbn. repeat split ; auto. apply NoDup_cons. intro HA.
       inversion HA ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros C HC. inversion HC ; subst ; auto. inversion H4 ; subst ; auto.
       contradiction.
       eapply MP. 2: apply Id ; exact Hor. apply Or_imp_assoc.
       apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma list_primeness_fst_Lind_pair : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  (forall x, In _ (fst (extension_theory Γ Δ)) (list_disj x) -> 
                       ((In _ (fst (extension_theory Γ Δ)) ⊥) \/ (exists A, List.In A x /\ (In _ (fst (extension_theory Γ Δ)) A)))).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. induction x.
- cbn in H0. left. auto.
- cbn. cbn in H0. apply primeness_fst_Lind_pair in H0 ; auto. destruct H0. right.
  exists a. auto. apply IHx in H0. destruct H0. left. auto.
  right. destruct H0. destruct H0. clear IHx. exists x0. auto.
Qed.


(* The extension witnesses existentials on the left. *)

Lemma Lwitness_Ex_help : forall A Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
   (fst (extension_theory Γ Δ)) (∃ A) ->
  (fst (nextension_theory Γ Δ (S (form_index (∃ A))))) A[($(form_index (∃ A)))..].
Proof.
intros.
pose (In_extension_In_form_index_L (∃ A) _ _ H H0 H1 H2).
cbn. unfold gen_choice_code.
rewrite form_enum_index. cbn.
right. split.
intro. destruct H3. cbn in H3. destruct H3. destruct H4.
apply (Under_extension_theory _ _ H H0 H1).
exists x. repeat split ; auto. intros. apply H4 in H6.
epose (extension_theory_extens_nextension _ _ _ A0). destruct a.
apply H8 in H6 ; auto.
eapply MP.
apply (FOBIH_Deduction_Theorem (∃ A) (list_disj x) (fst (extension_theory Γ Δ))) ; auto.
apply (FOBIH_monot _ _ H5) ; auto. intro. intros. inversion H6 ; subst ; auto. left.
epose (extension_theory_extens_nextension _ _ _ x0). destruct a.
apply H8 in H7 ; auto. inversion H7 ; subst.
right ; auto. apply Id ; auto. auto.
Qed.

Lemma Lind_pair_ex_henk : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  (ex_henk (fst (extension_theory Γ Δ))).
Proof.
intros Γ Δ H H0 H1 A HA. exists (form_index (∃ A)).
epose (extension_theory_extens_nextension (S (form_index (∃ A))) _ _ A[$(form_index (∃ A))..]). destruct a.
apply H2. apply Lwitness_Ex_help ; auto.
Qed.



(* The extension witnesses universals on the right. *)

Lemma Rwitness_All_help : forall A Γ Δ,
  closed_S Γ ->

  closed_S Δ ->
  ~ pair_der Γ Δ ->
   (snd (extension_theory Γ Δ)) (∀ A) ->
   (snd (nextension_theory Γ Δ (S (form_index (∀ A))))) A[($(form_index (∀ A)))..].
Proof.
intros.
pose (In_extension_In_form_index_R (∀ A) _ _ H H0 H1).
cbn. unfold gen_choice_code.
rewrite form_enum_index. cbn. right. split ; auto.
destruct (LEM (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∀ A)))) (Singleton form (∀ A)))
(snd (nextension_theory Γ Δ (form_index (∀ A)))))) ; auto.
exfalso.
apply (Under_nextension_theory (S (form_index (∀ A))) _ _ H H0 H1). exists [∀ A].
repeat split ; auto. apply NoDup_cons. intro. inversion H4. apply NoDup_nil. intros.
inversion H4. subst. apply s ; auto. inversion H5. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id. unfold In.
unfold gen_choice_code. rewrite form_enum_index ; cbn. right ; auto.
Qed.

Lemma Lind_pair_all_henk : forall Γ Δ,
  closed_S Γ ->
  closed_S Δ ->
  ~ pair_der Γ Δ ->
  (all_henk (fst (extension_theory Γ Δ))).
Proof.
intros Γ Δ H H0 H1 A HA. exists (form_index (∀ A)). intro.
assert (snd (extension_theory Γ Δ) (∀ A)).
{ epose (extension_theory_extens_nextension (S (form_index (∀ A))) _ _ (∀ A)).
  destruct a. destruct (form_index_In_L_or_R (∀ A) _ _ H H0 H1).
  + exfalso. apply HA. apply H3 ; auto.
  + apply H4 ; auto. }
apply Rwitness_All_help in H3 ; auto.
apply Under_extension_theory in H1 ; auto.
apply H1. exists [A[$(form_index (∀ A))..]].
repeat split ; auto.
- apply NoDup_cons. intros H4 ; inversion H4. apply NoDup_nil.
- intros B HB. inversion HB ; subst ; try contradiction.
  epose (extension_theory_extens_nextension (S (form_index (∀ A))) _ _ (A[$(form_index (∀ A))..])).
  destruct a. apply H5 ; auto.
- cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity.
  apply Id ; auto.
Qed.


End Properties_Lind.

(* ---------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we obtain the Lindenbaum lemma. *)

Open Scope type.

Lemma Stand_Lindenbaum_lemma_pair : forall Γ Δ,
    closed_S Γ ->
    closed_S Δ ->
    ~ pair_der Γ Δ ->
    existsT2 Γm, Included _ Γ Γm *
                   ded_clos Γm *
                   prime Γm *
                   ex_henk Γm *
                   all_henk Γm *
                   ~ pair_der Γm Δ.
Proof.
intros Γ Δ ClΓ ClΔ notder.
exists (fst (extension_theory Γ Δ)). repeat split.
- intro. apply extension_theory_extens.
- apply closeder_fst_Lind_pair ; auto ; apply cst_free_open_S ; auto.
- apply primeness_fst_Lind_pair ; auto ; apply cst_free_open_S ; auto.
- apply Lind_pair_ex_henk ; auto ; apply cst_free_open_S ; auto.
- apply Lind_pair_all_henk ; auto ; apply cst_free_open_S ; auto.
- intro. apply Under_extension_theory in notder ; auto.
  apply notder. destruct H as (l & Hl0 & Hl1 & Hl2).
  exists l ; repeat split ; auto. intros.
  apply extension_theory_extens ; auto.
Qed.

Lemma Stand_Lindenbaum_lemma : forall A,
    closed A ->
    ~ FOBIH_prv (Empty_set _) A ->
    existsT2 Γ, (~ Γ A) *
                   ded_clos Γ *
                   prime Γ *
                   ex_henk Γ *
                   all_henk Γ *
                   ~ FOBIH_prv Γ A.
Proof.
intros A cfA notder.
destruct (Stand_Lindenbaum_lemma_pair (Empty_set _) (Singleton _ A)) as (Γ & H0) ; auto.
- intros B HB. inversion HB.
- intros B HB. inversion HB ; subst ; auto.
- intro. apply notder. destruct H as (l & H0 & H1 & H2). cbn in *. destruct l ; cbn in *.
  eapply MP. apply Ax ; eapply A9 ; reflexivity. auto.
  destruct l. cbn in *. pose (H1 f). destruct s ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply imp_Id_gen. apply EFQ. auto. pose (H1 f). destruct s ; auto.
  pose (H1 f0). destruct s ; auto. right. apply in_eq. exfalso. inversion H0 ; subst. apply H4 ; apply in_eq.
- exists Γ. destruct H0. repeat destruct p. repeat split ; auto ; intro.
  + apply n. exists [A]. repeat split ; auto. apply NoDup_cons ; auto. apply NoDup_nil.
     intros. inversion H0 ; subst ; cbn. split. inversion H1.
     eapply MP. cbn in *. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
  + apply n. exists [A]. repeat split ; auto. apply NoDup_cons ; auto. apply NoDup_nil.
     intros. inversion H0 ; subst ; cbn. split. inversion H1.
     eapply MP. cbn in *. apply Ax ; eapply A3 ; reflexivity. auto.
Qed.


End Lindenbaum.

Print Assumptions Stand_Lindenbaum_lemma.
