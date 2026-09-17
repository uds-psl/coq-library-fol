Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.LogicalPrinciples.
Local Set Implicit Arguments.

(* Generalised blurred drinker paradoxes *)

Definition GenBDP_local B X (P : X -> Prop) :=
  exists f : B -> X, (forall b, P (f b)) -> forall x, P x.

Definition GenBDP_on B X :=
  forall (P : X -> Prop), GenBDP_local B P.

Definition GenBDP B := forall X, X -> GenBDP_on B X.

Definition GenBEP_local B X (P : X -> Prop) :=
  exists f : B -> X, (exists x, P x) -> exists b, P (f b).

Definition GenBEP_on B X :=
  forall (P : X -> Prop), GenBEP_local B P.

Definition GenBEP B := forall X, X -> GenBEP_on B X.

Lemma BDP_LEM :
  GenBDP bool -> LEM.
Proof.
  intros H P.
  destruct (H (sum P unit) (inr tt) (fun x => if x then False else True)) as [f Hf].
  destruct (f true) eqn : H1, (f false) eqn : H2; try tauto.
  right. intros HP. unshelve eapply (Hf _ (inl HP)).
  intros []; [ rewrite H1 | rewrite H2 ]; tauto.
Qed.

Lemma BDP_BEP B X (P : X -> Prop) :
  GenBEP_local B P -> GenBDP_local B (fun x => ~ P x).
Proof.
  intros [f Hf]. exists f. intros H x H'.
  destruct Hf as [b Hb].
  - now exists x.
  - now apply (H b).
Qed.

Definition GKS X :=
  forall P : Prop, exists f : X -> bool, P <-> exists x, f x = true.

Definition GKS' X :=
  forall P : Prop, exists f : X -> bool,
    (P -> ~ forall x, f x = false) /\ ((exists x, f x = true) -> P).

Lemma GKS_LEM :
  (GKS unit -> LEM) /\ (GKS' unit -> LEM).
Proof.
  split; intros HGKS P; destruct (HGKS P) as [f Hf].
  - destruct (f tt) eqn : Htt.
    + left. apply Hf. now exists tt.
    + right. intros [[] H] % Hf. congruence.
  - destruct (f tt) eqn : Htt.
    + left. apply Hf. now exists tt.
    + right. intros H % Hf. apply H. intros []. apply Htt.
Qed.

Lemma BDP_GKS B :
  (GenBDP B -> GKS' B) /\ (GenBEP B -> GKS B).
Proof.
  split; intros HB P.
  - destruct (HB (sum P unit) (inr tt) (fun x => if x then False else True)) as [f Hf].
    exists (fun b => if f b then true else false). split.
    + intros HP H. unshelve eapply (Hf _ (inl HP)).
      intros b. specialize (H b). destruct f; trivial. discriminate.
    + intros [b Hb]. destruct f; trivial. discriminate.
  - destruct (HB (sum P unit) (inr tt) (fun x => if x then True else False)) as [f Hf].
    exists (fun b => if f b then true else false). split.
    + intros HP. destruct Hf as [b Hb]; try now exists (inl HP).
      exists b. destruct f; trivial. contradiction.
    + intros [b Hb]. destruct f; trivial. discriminate.
Qed.

Definition GMP X :=
  forall f : X -> bool, ~ ~ (exists x, f x = true) -> exists x, f x = true.

Lemma GMP_unit :
  GMP unit.
Proof.
  intros f Hf. exists tt. destruct f eqn : Htt; trivial.
  contradict Hf. intros [[] H]. congruence.
Qed.

Lemma BDP_GMP B (b0 : B) :
  (LEM <-> GenBDP B /\ GMP B) /\ (LEM <-> GenBEP B /\ GMP B).
Proof.
  split; split; try split. 
  - intros X x0 P. destruct DP_iff_LEM as [_ H'].
    destruct (H' H X x0 P) as [f Hf]. exists (fun _ => f tt).
    intros HP. apply Hf. intros [].  now apply HP.
  - intros f. now apply LEM_iff_DN.
  - intros [H1 H2]. apply LEM_iff_DN. intros P.
    apply BDP_GKS in H1. destruct (H1 P) as [f Hf].
    intros HP. apply Hf, H2. intros H'. apply HP.
    intros HP' % Hf. apply HP'. intros b.
    destruct f eqn : Hb; trivial. contradict H'. now exists b.
  - intros X x0 P. destruct EP_iff_LEM as [_ H'].
    destruct (H' H X x0 P) as [f Hf]. exists (fun _ => f tt).
    intros [[] HP] % Hf. now exists b0.
  - intros f. now apply LEM_iff_DN.
  - intros [H1 H2]. apply LEM_iff_DN. intros P.
    apply BDP_GKS in H1. destruct (H1 P) as [f Hf].
    intros HP. apply Hf, H2. intros H'. apply HP.
    intros HP' % Hf. now contradict H'.
Qed.

(* Generalised blurred choice axioms *)

Definition GenBDC_on B X := forall (R : X -> X -> Prop),
  total R -> exists f : B -> X, total (R ∘ f).

Definition GenBDC B := forall X, X -> GenBDC_on B X.

Definition GenDDC_on B X := forall (R : X -> X -> Prop),
  direct R -> exists f : B -> X, direct (R ∘ f).

Definition GenDDC B := forall X, X -> GenDDC_on B X.

Definition BAC_on B Y := forall (R : B -> Y -> Prop),
  total R -> exists f : B -> Y, forall b, exists b', R b (f b').

Definition BAC B := forall Y, BAC_on B Y.

Lemma AC_BAC B :
  (forall Y, AC_on B Y) <-> (forall Y, BAC_on B Y) /\ AC_on B B.
Proof.
  split.
  - intros H. split; try apply H.
    intros Y R HR. destruct (H Y R HR) as [f Hf].
    exists f. intros b. exists b. apply Hf.
  - intros [H1 H2] Y R HR.
    destruct (H1 Y R HR) as [f Hf].
    destruct (H2 (fun b b' => R b (f b'))) as [g Hg].
    + intros b. apply Hf.
    + exists (fun b => f (g b)). apply Hg.
Qed.

(* Generalised DLS reverse analysis *)

Section DLS_rev.

  Variable B : Type.
  Variable b0 : B.

  Instance Bsig_funcs : funcs_signature :=
    { syms := False; ar_syms := fun _ => 42}.

  Instance Bsig_preds : preds_signature :=
    { preds := B; ar_preds := fun _ => 1}.

  Definition GenDLS :=
    forall M : model, exists I : interp B, Build_model I ⪳ M.

  Instance BDP_interp X (P : X -> Prop) : interp X :=
    { i_func := fun f v => match f with end; i_atom := fun b v => P (hd v) }.

  Definition BDP_model X (P : X -> Prop) : model :=
    {| domain := X; interp' := BDP_interp P |}.

  Definition x1 : vec term 1 :=
    (cons _ $0 _ (nil _)).

  Definition Px1 : form :=
    atom b0 x1.

  Lemma GenDLS_GenBDP :
    GenDLS -> GenBDP B.
  Proof.
    intros HDLS X x0 P.
    destruct (HDLS (BDP_model P)) as [I [h Hh]].
    exists h. intros H x.
    apply (Hh (∀ Px1) (fun _ => b0)).
    intros b. apply Hh. apply H.
  Qed.

  Lemma GenDLS_GenBEP :
    GenDLS -> GenBEP B.
  Proof.
    intros HDLS X x0 P.
    destruct (HDLS (BDP_model P)) as [I [h Hh]].
    exists h. intros H.
    destruct (Hh (∃ Px1) (fun _ => b0)) as [_ [b Hb]].
    - apply H.
    - exists b. apply Hh in Hb. apply Hb.
  Qed.

  Instance BAC_interp Y (R : B -> Y -> Prop) : interp Y :=
    { i_func := fun f v => match f with end; i_atom := fun b v => R b (hd v) }.

  Definition BAC_model Y (R : B -> Y -> Prop) : model :=
    {| domain := Y; interp' := BAC_interp R |}.

  Definition Rbx1 (b : B) : form :=
    atom b x1.

  Lemma GenDLS_BAC :
    GenDLS -> BAC B.
  Proof.
    intros HDLS Y R HR.
    destruct (HDLS (BAC_model R)) as [I [h Hh]].
    exists h. intros b.
    destruct (Hh (∃ Rbx1 b) (fun _ => b0)) as [_ [b' Hb]].
    - apply HR.
    - exists b'. apply Hh in Hb. apply Hb.
  Qed.

  Instance Bsig_preds2 : preds_signature :=
    { preds := B; ar_preds := fun _ => 2}.

  Definition GenDLS2 :=
    forall M : model, exists I : interp B, Build_model I ⪳ M.

  Instance DDC_interp X (R : X -> X -> Prop) : interp X :=
    { i_func := fun f v => match f with end; i_atom := fun b v => R (hd v) (hd (tl v)) }.

  Definition DDC_model X (R : X -> X -> Prop) : model :=
    {| domain := X; interp' := DDC_interp R |}.

  Definition x1x3 : vec term 2 :=
    (cons _ $1 _ (cons _ $0 _ (nil _))).

  Definition x2x3 : vec term 2 :=
    (cons _ $2 _ (cons _ $0 _ (nil _))).

  Definition Rx1x3 : form :=
    atom b0 x1x3.

  Definition Rx2x3 : form :=
    atom b0 x2x3.

  Lemma GenDLS_GenDDC :
    GenDLS2 -> GenDDC B.
  Proof.
    intros HDLS X x0 R HR.
    destruct (HDLS (DDC_model R)) as [I [h Hh]].
    exists h. intros b1 b2.
    destruct (Hh (∃ Rx1x3 ∧ Rx2x3) (fun n => if n then b1 else b2)) as [_ [b' Hb]].
    - apply (HR (h b1) (h b2)).
    - exists b'. apply Hh in Hb. apply Hb.
  Qed.

End DLS_rev.

