Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.DCPre.

(** * Reverse Analysis: DC-Delta *)

Section DC.

    Existing Instance sig_empty.
    Existing Instance sig_binary.

    Fact Σ_countable: countable_sig.
    Proof.
        repeat split.
        - exists (fun _ => None). intros [].
        - exists (fun _ => Some  tt). intros []. exists 42; eauto.
        - intros []. - intros [] []; firstorder.
    Qed.

    Variable A: Type.
    Variable a: A.
    Variable R: A -> A -> Prop.

    Instance interp__A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun P v => R (hd v) (last v)
    }.

    Definition Model__A: model :=
    {|
        domain := A;
        interp' := interp__A
    |}.

    Definition total_form :=
        ∀ (∃ (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _))))).
    Definition forfor_form :=
        (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _)))).

    Lemma total_sat:
        forall h, (forall x, exists y, R x y) -> Model__A ⊨[h] total_form.
    Proof.
        cbn; intros.
        destruct (H d) as [e P].
        now exists e.
    Qed.

    Definition p {N} (α β: N): env N :=
        fun n => match n with
            | 0 => β
            | _ => α end.

    Lemma forfor_sat {N} (h: N -> A) (α β: N):
        R (h α) (h β) <-> Model__A ⊨[(p α β) >> h] forfor_form.
    Proof.
        unfold ">>"; now cbn.
    Qed.

    Lemma exists_next:
    forall B (R': B -> B -> Prop), coutable_model B ->
        (forall x, exists y, R' x y) -> exists f: nat -> B,
            forall b, exists n, R' b (f n).
    Proof.
        intros B R' (f & h & sur) total.
        exists f. intro b.
        destruct (total b) as [c Rbc].
        exists (h c). now rewrite sur.
    Qed.    

    Section dec__R_full.

    Definition dec_R := forall x y, dec (R x y).

    Lemma LS_impl_DC: DLS -> dec_R -> DC_on' R.
    Proof using a.
        intros LS DecR  total.
        destruct (LS sig_empty sig_binary Σ_countable Model__A a) as [N [(h & g & Hh) [f HN]]].
        specialize (@total_sat ((fun _ => (h 42)) >> f) total ) as total'.
        apply HN in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (f  α) (f β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in HN; rewrite <- HN.
        destruct H as [R' [P1 P2]].
        assert (forall x y, dec (R' x y)) as dec__R'.
        { intros x y. destruct (DecR (f x) (f y)); firstorder. }
        assert (forall n : N, exists m : nat, h m = n) as Ht.
        { intro n. exists (g n). now rewrite Hh. }
        destruct (@DC_ω _ _ h Ht dec__R' P1 (h 42)) as [g' [case0 Choice]].
        exists (g' >> f); unfold ">>". 
        intro n'; now rewrite <- (P2 (g' n') (g' (S n'))).
    Qed.

    End dec__R_full.

End DC.

Section DCRes.

    Theorem LS_impl_DC_delta: DLS -> DC__Δ .
    Proof.
        intros H X R dec_R x tot_R.
        apply LS_impl_DC; eauto.
    Qed.

End DCRes.


















