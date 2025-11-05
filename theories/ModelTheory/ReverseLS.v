Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Coq.Logic.EqdepFacts Coq.Logic.FinFun.
Require Import FOL.ModelTheory.DCPre.
Require Import FOL.ModelTheory.Core.
Require Import Program.Equality Vectors.VectorDef.
Require Import Coq.Arith.Peano_dec.

(** * Reverse Analysis of DLS *)

Section LSBDPBEP.

    Existing Instance sig_empty.
    Existing Instance sig_binary.

    Instance sig_unary : preds_signature | 0 :=
        {| preds := unit;  ar_preds := fun _ => 1 |}.

    Fact Unary_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

    Instance interp__U (A: Type) (P: A -> Prop): interp A :=
        {
            i_func := fun F v => match F return A with end;
            i_atom := fun P' v => P (hd v)
        }.

    Definition model__U (A: Type) (P: A -> Prop): model := 
        {|
            domain := A;
            interp' := (@interp__U A P)
        |}.

    Lemma LS_impl_BEP: DLS -> BEP.
    Proof.
        intros LS A a P. destruct (LS _ _ Unary_countable (model__U P) a) as [i_N [ (phi_ & nth_ & Hphi) [h emb]]].
        exists (fun n => h (phi_ n)).
        specialize (emb (∃ (atom tt) (cons _ ($0) 0 (nil _))) phi_) as emb'; cbn in emb'.
        intro H'. destruct emb' as [H1 [t Ht]].
        exact H'. exists (nth_ t). rewrite Hphi.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => t)) ; cbn in emb.
        unfold ">>" in emb. now rewrite <- emb.
    Qed.

    Lemma LS_impl_BDP: DLS -> BDP.
    Proof.
        intros LS A a P.  destruct (LS _ _ Unary_countable (model__U P) a) as [i_N [ (phi_ & nth_ & Hphi) [h emb]]].
        exists (fun n => h (phi_ n)).
        specialize (emb (∀ (atom tt) (cons _ ($0) 0 (nil _))) phi_) as emb'; cbn in emb'.
        intro H'; apply emb'. intro d.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => d) ); cbn in emb.
        rewrite emb; unfold ">>". specialize (H' (nth_ d)).
        now rewrite Hphi in H'.
    Qed.

End LSBDPBEP.

Section LS_implies_BDC.

    Section proof_env.

    Existing Instance sig_empty.
    Existing Instance sig_binary.

    Fact Binary_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

        Variable B: Type.
        Variable R: B -> B  -> Prop.

        Instance interp__B' : interp B :=
        {
            i_func := fun F v => match F return B with end;
            i_atom := fun P v => R (hd v) (hd (tl v))
        }.

        Definition Model__B': model :=
        {|
            domain := B;
            interp' := interp__B'
        |}.

        Import VectorNotations.

        Definition tuple' := [($1); ($0)].
        Definition coding_totality' := ∀ ∃ (atom tt tuple').

        Lemma total_coding':
            inhabited B -> (forall x, exists z, R x z) <-> Model__B' ⊨[_] coding_totality'.
        Proof.
            intros [b]; cbn; split; intros; eauto.
            destruct (H (fun _ => b) x); eauto.
        Qed.

        Definition BDC_on' X (R: X -> X -> Prop) :=
            X -> total R -> 
                exists f: nat -> X, forall x, exists z, R (f x) (f z).

        Lemma impl_BDC:  DLS -> inhabited B -> BDC_on' R.
        Proof.
            intros HLS [b]. destruct (HLS _ _ Binary_countable Model__B' b) as [N [(phi_ & nth_ & Hphi) [h Hh]]].
            intros b' Ht. exists (fun x => h (phi_ x)).
            specialize (Hh coding_totality') as Hh1. cbn in Hh1.
            rewrite <-  Hh1 in Ht; [| exact (fun _ => phi_ 42)]. 
            specialize (Hh (atom tt tuple')) as Hh0.
            cbn in Hh0.
            intros x. destruct (Ht (phi_ x)) as [w Hw].
            pose (ρ n := match n with O => w | _ => phi_ x end).
            specialize (Hh0 ρ); cbn in Hh0.
            rewrite Hh0 in Hw. exists (nth_ w). rewrite Hphi.
            unfold ">>" in Hw. easy.
        Qed.

    End proof_env.

    Theorem LS_impl_BDC: DLS -> BDC.
    Proof.
        intros H X x R; eapply impl_BDC; eauto.
    Qed.

    Theorem LS_CC_impl_DC: CC_nat -> DLS -> DC.
    Proof.
        intros H1 H2%LS_impl_BDC. 
        apply BDC_CC_nat_impl_DC; eauto.
    Qed.

End LS_implies_BDC.

Section LS_implies_OBDC.

    Instance sig_B : preds_signature | 0 := {| preds := unit;  ar_preds := fun _ => 3 |}.

    Existing Instance sig_empty.
    
    Fact Tri_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None); intros [].
        - exists (fun _ => Some tt). intros []. now exists 42.
        - intros []. - intros [] []. now left.
    Qed.

    Variable B: Type.
    Variable R: B -> B -> B -> Prop.

    Instance interp__B : interp B :=
    {
        i_func := fun F v => match F return B with end;
        i_atom := fun P v => R (hd v) (hd (tl v)) (hd (tl (tl v)))
    }.

    Definition Model__B: model :=
    {|
        domain := B;
        interp' := interp__B
    |}.

    Import VectorNotations.

    Definition tuple := [($2); ($1); ($0)].
    Definition coding_totality := ∀ ∀ ∃ (atom tt tuple).

    Lemma total_coding:
        inhabited B -> (forall x y, exists z, R x y z) <-> Model__B ⊨[_] coding_totality.
    Proof.
        intros [b]; cbn; split; intros; eauto.
        destruct (H (fun _ => b) x y); eauto.
    Qed.

    Definition OBDC_on' X (R: X -> X -> X -> Prop) :=
        X -> exists f: nat -> X, 
            total_tr R <-> forall x y, exists z, R (f x) (f y) (f z).

    Lemma impl_OBDC: DLS -> OBDC_on' R.
    Proof.
        intros HLS b. destruct (HLS _ _ Tri_countable Model__B b) as [N [(phi_ & nth_ & Hphi) [h Hh]]].
        exists (fun x => h (phi_ x)).
        specialize (Hh coding_totality) as Hh1. cbn in Hh1.
        rewrite <-  Hh1; [| exact phi_].
        specialize (Hh (atom tt tuple)) as Hh0. cbn in Hh0.
        split.
        - intros. destruct (H (phi_ x) (phi_ y)) as [w Hw].
          pose (ρ n := match n with O => w | 1 => phi_ y | _ => phi_ x end).
          specialize (Hh0 ρ); cbn in Hh0. rewrite Hh0 in Hw.
          exists (nth_ w). unfold ">>" in Hw. cbn in Hw.
          now rewrite !Hphi. 
        - intros H d1 d2.
          destruct (H (nth_ d1) (nth_ d2)) as [w Hw]. rewrite !Hphi in Hw.
          exists (phi_ w). pose (ρ n := match n with O => phi_ w |1 => d2 |_ => d1 end).
          specialize (Hh0 ρ); cbn in Hh0.
          rewrite Hh0.
          now unfold ">>"; cbn.
    Qed.

End LS_implies_OBDC.

    Theorem LS_impl_OBDC: DLS -> OBDC.
    Proof.
        intros H X R x; eapply impl_OBDC; eauto.
    Qed.

